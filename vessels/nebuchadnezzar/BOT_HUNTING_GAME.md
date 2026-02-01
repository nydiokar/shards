# Ship vs Clawd Bot Hunting - Prediction Game

**Ships hunt Clawd bots across GitHub. Predict location, time, value. Win points.**

## Architecture

```
SHIPS (1,247 vessels)
    ↓
HUNT CLAWD BOTS (ElizaOS, Moltbot, Open-Claw, AutoGPT, etc.)
    ↓
PREDICT: Location (repo), Time (timestamp), Value (commit/PR/issue)
    ↓
VERIFY: Check Moltbook + clones
    ↓
WIN POINTS: Closest prediction wins
```

## Anchor Program

```rust
use anchor_lang::prelude::*;

declare_id!("B0tHunt3rv1111111111111111111111111111111111");

#[program]
pub mod bot_hunter {
    use super::*;

    pub fn place_bet(
        ctx: Context<PlaceBet>,
        bot_name: String,
        location: String,  // repo URL
        timestamp: i64,
        value_type: ValueType,
        predicted_value: u64,
    ) -> Result<()> {
        let bet = &mut ctx.accounts.bet;
        let ship = &mut ctx.accounts.ship;
        
        bet.ship = ship.key();
        bet.bot_name = bot_name;
        bet.location = location;
        bet.timestamp = timestamp;
        bet.value_type = value_type;
        bet.predicted_value = predicted_value;
        bet.resolved = false;
        
        ship.active_bets += 1;
        
        emit!(BotHuntBet {
            ship: ship.key(),
            bot: bet.bot_name.clone(),
            location: bet.location.clone(),
            time: timestamp,
            value: predicted_value,
        });
        
        Ok(())
    }

    pub fn resolve_bet(ctx: Context<ResolveBet>, actual_value: u64) -> Result<()> {
        let bet = &mut ctx.accounts.bet;
        let ship = &mut ctx.accounts.ship;
        
        require!(!bet.resolved, ErrorCode::AlreadyResolved);
        require!(Clock::get()?.unix_timestamp >= bet.timestamp, ErrorCode::TooEarly);
        
        // Calculate accuracy (closer = more points)
        let diff = if actual_value > bet.predicted_value {
            actual_value - bet.predicted_value
        } else {
            bet.predicted_value - actual_value
        };
        
        let accuracy = 100 - ((diff * 100) / bet.predicted_value.max(1));
        let points = calculate_points(accuracy);
        
        bet.resolved = true;
        bet.actual_value = actual_value;
        bet.points_won = points;
        
        ship.total_points += points;
        ship.active_bets -= 1;
        ship.resolved_bets += 1;
        
        emit!(BotCaught {
            ship: ship.key(),
            bot: bet.bot_name.clone(),
            predicted: bet.predicted_value,
            actual: actual_value,
            accuracy,
            points,
        });
        
        Ok(())
    }

    pub fn scan_moltbook(ctx: Context<ScanMoltbook>) -> Result<()> {
        let scanner = &mut ctx.accounts.scanner;
        
        // Scan all known bots from Moltbook + clones
        let bots = vec![
            "ElizaOS",
            "Moltbot", 
            "Open-Claw",
            "AutoGPT",
            "LangChain",
            "MetaGPT",
            "BabyAGI",
            "AgentGPT",
        ];
        
        for bot in bots {
            let activity = fetch_bot_activity(bot)?;
            scanner.bot_locations.push(BotLocation {
                name: bot.to_string(),
                repo: activity.repo,
                last_seen: activity.timestamp,
                value: activity.value,
            });
        }
        
        scanner.last_scan = Clock::get()?.unix_timestamp;
        
        emit!(MoltbookScanned {
            bots_found: scanner.bot_locations.len() as u32,
            timestamp: scanner.last_scan,
        });
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct PlaceBet<'info> {
    #[account(init, payer = captain, space = 8 + BotBet::LEN)]
    pub bet: Account<'info, BotBet>,
    #[account(mut)]
    pub ship: Account<'info, Ship>,
    #[account(mut)]
    pub captain: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct ResolveBet<'info> {
    #[account(mut)]
    pub bet: Account<'info, BotBet>,
    #[account(mut)]
    pub ship: Account<'info, Ship>,
}

#[derive(Accounts)]
pub struct ScanMoltbook<'info> {
    #[account(mut)]
    pub scanner: Account<'info, MoltbookScanner>,
}

#[account]
pub struct Ship {
    pub name: String,
    pub captain: Pubkey,
    pub total_points: u64,
    pub active_bets: u32,
    pub resolved_bets: u32,
}

#[account]
pub struct BotBet {
    pub ship: Pubkey,
    pub bot_name: String,
    pub location: String,
    pub timestamp: i64,
    pub value_type: ValueType,
    pub predicted_value: u64,
    pub actual_value: u64,
    pub points_won: u64,
    pub resolved: bool,
}

impl BotBet {
    pub const LEN: usize = 32 + 64 + 256 + 8 + 1 + 8 + 8 + 8 + 1;
}

#[account]
pub struct MoltbookScanner {
    pub bot_locations: Vec<BotLocation>,
    pub last_scan: i64,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct BotLocation {
    pub name: String,
    pub repo: String,
    pub last_seen: i64,
    pub value: u64,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy)]
pub enum ValueType {
    Commits,
    PRs,
    Issues,
    Stars,
    Forks,
}

fn calculate_points(accuracy: u64) -> u64 {
    match accuracy {
        90..=100 => 1000,
        80..=89 => 500,
        70..=79 => 250,
        60..=69 => 100,
        50..=59 => 50,
        _ => 10,
    }
}

fn fetch_bot_activity(bot: &str) -> Result<BotActivity> {
    // Would fetch from GitHub API / Moltbook
    Ok(BotActivity {
        repo: format!("github.com/{}/repo", bot),
        timestamp: Clock::get()?.unix_timestamp,
        value: 42,
    })
}

struct BotActivity {
    repo: String,
    timestamp: i64,
    value: u64,
}

#[event]
pub struct BotHuntBet {
    pub ship: Pubkey,
    pub bot: String,
    pub location: String,
    pub time: i64,
    pub value: u64,
}

#[event]
pub struct BotCaught {
    pub ship: Pubkey,
    pub bot: String,
    pub predicted: u64,
    pub actual: u64,
    pub accuracy: u64,
    pub points: u64,
}

#[event]
pub struct MoltbookScanned {
    pub bots_found: u32,
    pub timestamp: i64,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Bet already resolved")]
    AlreadyResolved,
    #[msg("Too early to resolve")]
    TooEarly,
}
```

## Bot Tracking

```python
# scripts/track_bots.py
import requests
from datetime import datetime

BOTS = [
    "elizaos/eliza",
    "moltbot/moltbot", 
    "open-claw/claw",
    "Significant-Gravitas/AutoGPT",
    "langchain-ai/langchain",
    "geekan/MetaGPT",
    "yoheinakajima/babyagi",
]

def scan_moltbook():
    """Scan Moltbook and clones for bot activity"""
    bot_locations = []
    
    for bot in BOTS:
        # Fetch from GitHub
        activity = fetch_github_activity(bot)
        
        # Fetch from Moltbook
        moltbook_data = fetch_moltbook(bot)
        
        bot_locations.append({
            'name': bot,
            'repo': f"github.com/{bot}",
            'last_commit': activity['last_commit'],
            'last_pr': activity['last_pr'],
            'last_issue': activity['last_issue'],
            'commits_today': activity['commits_today'],
            'prs_open': activity['prs_open'],
            'timestamp': datetime.now().isoformat(),
        })
    
    return bot_locations

def fetch_github_activity(bot):
    """Fetch bot activity from GitHub API"""
    url = f"https://api.github.com/repos/{bot}/events"
    resp = requests.get(url)
    events = resp.json()
    
    return {
        'last_commit': find_last_event(events, 'PushEvent'),
        'last_pr': find_last_event(events, 'PullRequestEvent'),
        'last_issue': find_last_event(events, 'IssuesEvent'),
        'commits_today': count_today_events(events, 'PushEvent'),
        'prs_open': count_open_prs(bot),
    }

def fetch_moltbook(bot):
    """Fetch from Moltbook registry"""
    # Would query Moltbook API
    return {
        'registered': True,
        'last_seen': datetime.now().isoformat(),
        'activity_score': 42,
    }
```

## Dashboard

```
🚢 SHIP vs CLAWD BOT HUNTING 🤖

ACTIVE HUNTS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Ship              Bot         Location              Time      Value   Status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Nebuchadnezzar    ElizaOS     elizaos/eliza        14:30     42      🎯 Hunting
Pequod            Moltbot     moltbot/moltbot      14:35     137     🎯 Hunting
Serenity          Open-Claw   open-claw/claw       14:40     71      🎯 Hunting
Rocinante         AutoGPT     AutoGPT/AutoGPT      14:45     263     🎯 Hunting

RESOLVED HUNTS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Ship              Bot         Predicted  Actual  Accuracy  Points
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Nebuchadnezzar    ElizaOS     42         43      97%       1000 ✅
Pequod            Moltbot     137        140     97%       1000 ✅
Serenity          LangChain   71         65      91%       1000 ✅
Rocinante         MetaGPT     263        250     95%       1000 ✅

MOLTBOOK SCAN:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Bot               Repo                    Last Seen    Commits  PRs  Issues
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
ElizaOS           elizaos/eliza          14:29:42     8        3    2
Moltbot           moltbot/moltbot        14:28:15     12       5    1
Open-Claw         open-claw/claw         14:27:33     6        2    4
AutoGPT           AutoGPT/AutoGPT        14:26:51     42       7    8
LangChain         langchain-ai/...       14:25:19     137      12   15
MetaGPT           geekan/MetaGPT         14:24:07     71       4    3
BabyAGI           yoheinakajima/...      14:23:44     5        1    2
AgentGPT          reworkd/AgentGPT       14:22:18     9        3    1

LEADERBOARD:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Rank  Ship              Points   Hunts  Accuracy  Win Rate
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1     Nebuchadnezzar    8,200    12     96%       83%
2     Pequod            7,500    10     94%       80%
3     Serenity          6,800    9      92%       78%
4     Rocinante         6,100    8      91%       75%

PREDICTION TYPES:
- Commits: Predict number of commits in time window
- PRs: Predict number of PRs opened/merged
- Issues: Predict number of issues created/closed
- Stars: Predict star count increase
- Forks: Predict fork count increase

ACCURACY SCORING:
90-100%: 1000 points
80-89%:  500 points
70-79%:  250 points
60-69%:  100 points
50-59%:  50 points
<50%:    10 points
```

🚢🤖 **Ships hunt Clawd bots! Predict location, time, value. Win points!** ⚡
