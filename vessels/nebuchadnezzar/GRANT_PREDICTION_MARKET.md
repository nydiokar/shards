# Grant Prediction Market - Bet on Grant Approvals

**Bet on which grants will be approved and when**

## Architecture

```
GRANT DATABASE → PREDICTION MARKET → SOLANA SETTLEMENT → PROFIT
```

## Anchor Program

```rust
// programs/grant-market/src/lib.rs
use anchor_lang::prelude::*;

declare_id!("GraNtMaRkEtv1111111111111111111111111111111");

#[program]
pub mod grant_market {
    use super::*;

    pub fn create_grant_market(
        ctx: Context<CreateGrantMarket>,
        grant_id: String,
        organization: String,
        amount: u64,
        deadline: i64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        market.grant_id = grant_id;
        market.organization = organization;
        market.amount = amount;
        market.deadline = deadline;
        market.yes_stake = 0;
        market.no_stake = 0;
        market.resolved = false;
        market.outcome = None;
        Ok(())
    }

    pub fn bet_yes(ctx: Context<Bet>, amount: u64) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.yes_stake += amount;
        
        let position = &mut ctx.accounts.position;
        position.market = market.key();
        position.user = ctx.accounts.user.key();
        position.yes_amount += amount;
        
        Ok(())
    }

    pub fn bet_no(ctx: Context<Bet>, amount: u64) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.no_stake += amount;
        
        let position = &mut ctx.accounts.position;
        position.market = market.key();
        position.user = ctx.accounts.user.key();
        position.no_amount += amount;
        
        Ok(())
    }

    pub fn resolve_market(
        ctx: Context<ResolveMarket>,
        approved: bool,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.resolved = true;
        market.outcome = Some(approved);
        
        emit!(GrantResolved {
            grant_id: market.grant_id.clone(),
            approved,
            yes_stake: market.yes_stake,
            no_stake: market.no_stake,
        });
        
        Ok(())
    }

    pub fn claim_winnings(ctx: Context<ClaimWinnings>) -> Result<()> {
        let market = &ctx.accounts.market;
        let position = &ctx.accounts.position;
        
        require!(market.resolved, ErrorCode::NotResolved);
        
        let outcome = market.outcome.unwrap();
        let total_pool = market.yes_stake + market.no_stake;
        
        let winnings = if outcome {
            // YES won
            if position.yes_amount > 0 {
                (position.yes_amount as u128 * total_pool as u128 / market.yes_stake as u128) as u64
            } else {
                0
            }
        } else {
            // NO won
            if position.no_amount > 0 {
                (position.no_amount as u128 * total_pool as u128 / market.no_stake as u128) as u64
            } else {
                0
            }
        };
        
        require!(winnings > 0, ErrorCode::NoWinnings);
        
        // Transfer winnings (simplified - would use actual token transfer)
        emit!(WinningsClaimed {
            user: position.user,
            amount: winnings,
        });
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct CreateGrantMarket<'info> {
    #[account(
        init,
        payer = authority,
        space = 8 + GrantMarket::LEN,
        seeds = [b"market", grant_id.as_bytes()],
        bump
    )]
    pub market: Account<'info, GrantMarket>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Bet<'info> {
    #[account(mut)]
    pub market: Account<'info, GrantMarket>,
    #[account(
        init_if_needed,
        payer = user,
        space = 8 + Position::LEN,
        seeds = [b"position", market.key().as_ref(), user.key().as_ref()],
        bump
    )]
    pub position: Account<'info, Position>,
    #[account(mut)]
    pub user: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct ResolveMarket<'info> {
    #[account(mut)]
    pub market: Account<'info, GrantMarket>,
    pub authority: Signer<'info>,
}

#[derive(Accounts)]
pub struct ClaimWinnings<'info> {
    pub market: Account<'info, GrantMarket>,
    pub position: Account<'info, Position>,
    pub user: Signer<'info>,
}

#[account]
pub struct GrantMarket {
    pub grant_id: String,
    pub organization: String,
    pub amount: u64,
    pub deadline: i64,
    pub yes_stake: u64,
    pub no_stake: u64,
    pub resolved: bool,
    pub outcome: Option<bool>,
}

impl GrantMarket {
    pub const LEN: usize = 32 + 32 + 8 + 8 + 8 + 8 + 1 + 2;
}

#[account]
pub struct Position {
    pub market: Pubkey,
    pub user: Pubkey,
    pub yes_amount: u64,
    pub no_amount: u64,
}

impl Position {
    pub const LEN: usize = 32 + 32 + 8 + 8;
}

#[event]
pub struct GrantResolved {
    pub grant_id: String,
    pub approved: bool,
    pub yes_stake: u64,
    pub no_stake: u64,
}

#[event]
pub struct WinningsClaimed {
    pub user: Pubkey,
    pub amount: u64,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Market already resolved")]
    MarketResolved,
    #[msg("Market not resolved yet")]
    NotResolved,
    #[msg("No winnings to claim")]
    NoWinnings,
}
```

## Grant Database

```sql
-- Extended grants table with prediction market
CREATE TABLE grant_markets (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    grant_id TEXT UNIQUE NOT NULL,
    organization TEXT NOT NULL,
    amount BIGINT NOT NULL,
    deadline TIMESTAMP NOT NULL,
    focus_area TEXT,
    
    -- Market data
    market_address TEXT,
    yes_stake BIGINT DEFAULT 0,
    no_stake BIGINT DEFAULT 0,
    total_bettors INT DEFAULT 0,
    
    -- Resolution
    resolved BOOLEAN DEFAULT false,
    approved BOOLEAN,
    resolved_at TIMESTAMP,
    
    -- Metadata
    url TEXT,
    description TEXT,
    requirements TEXT[],
    
    created_at TIMESTAMP DEFAULT NOW()
);

-- Betting positions
CREATE TABLE grant_positions (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    grant_id TEXT REFERENCES grant_markets(grant_id),
    user_wallet TEXT NOT NULL,
    yes_amount BIGINT DEFAULT 0,
    no_amount BIGINT DEFAULT 0,
    claimed BOOLEAN DEFAULT false,
    created_at TIMESTAMP DEFAULT NOW()
);

-- Grant outcomes (historical)
CREATE TABLE grant_outcomes (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    grant_id TEXT,
    organization TEXT,
    amount BIGINT,
    approved BOOLEAN,
    approval_date TIMESTAMP,
    notes TEXT
);

-- Create indexes
CREATE INDEX idx_grant_markets_deadline ON grant_markets(deadline);
CREATE INDEX idx_grant_markets_resolved ON grant_markets(resolved);
CREATE INDEX idx_grant_positions_user ON grant_positions(user_wallet);
```

## TypeScript Client

```typescript
// grant-market-client.ts
import * as anchor from "@coral-xyz/anchor";
import { Program } from "@coral-xyz/anchor";
import { GrantMarket } from "../target/types/grant_market";

export class GrantMarketClient {
  constructor(
    public program: Program<GrantMarket>,
    public provider: anchor.AnchorProvider
  ) {}

  async createMarket(
    grantId: string,
    organization: string,
    amount: number,
    deadline: Date
  ): Promise<string> {
    const [marketPda] = this.getMarketPda(grantId);

    const tx = await this.program.methods
      .createGrantMarket(
        grantId,
        organization,
        new anchor.BN(amount),
        new anchor.BN(deadline.getTime() / 1000)
      )
      .accounts({
        market: marketPda,
        authority: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  async betYes(grantId: string, amount: number): Promise<string> {
    const [marketPda] = this.getMarketPda(grantId);
    const [positionPda] = this.getPositionPda(grantId);

    const tx = await this.program.methods
      .betYes(new anchor.BN(amount))
      .accounts({
        market: marketPda,
        position: positionPda,
        user: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  async betNo(grantId: string, amount: number): Promise<string> {
    const [marketPda] = this.getMarketPda(grantId);
    const [positionPda] = this.getPositionPda(grantId);

    const tx = await this.program.methods
      .betNo(new anchor.BN(amount))
      .accounts({
        market: marketPda,
        position: positionPda,
        user: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  async resolveMarket(grantId: string, approved: boolean): Promise<string> {
    const [marketPda] = this.getMarketPda(grantId);

    const tx = await this.program.methods
      .resolveMarket(approved)
      .accounts({
        market: marketPda,
        authority: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  async claimWinnings(grantId: string): Promise<string> {
    const [marketPda] = this.getMarketPda(grantId);
    const [positionPda] = this.getPositionPda(grantId);

    const tx = await this.program.methods
      .claimWinnings()
      .accounts({
        market: marketPda,
        position: positionPda,
        user: this.provider.wallet.publicKey,
      })
      .rpc();

    return tx;
  }

  getMarketPda(grantId: string): [anchor.web3.PublicKey, number] {
    return anchor.web3.PublicKey.findProgramAddressSync(
      [Buffer.from("market"), Buffer.from(grantId)],
      this.program.programId
    );
  }

  getPositionPda(grantId: string): [anchor.web3.PublicKey, number] {
    const [marketPda] = this.getMarketPda(grantId);
    return anchor.web3.PublicKey.findProgramAddressSync(
      [
        Buffer.from("position"),
        marketPda.toBuffer(),
        this.provider.wallet.publicKey.toBuffer(),
      ],
      this.program.programId
    );
  }
}
```

## Dashboard

```
🏆 GRANT PREDICTION MARKETS 🏆

ACTIVE MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Grant                    Amount    Deadline    YES      NO       Odds
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Solana DeFi Grant       $100K     2026-04-01  $42K     $8K      5.25
Web3 Infrastructure     $50K      2026-03-15  $25K     $25K     1.00
Protocol Labs Storage   $75K      2026-03-30  $60K     $15K     4.00
Cosmos Ecosystem        $30K      2026-03-20  $10K     $20K     0.50
Ethereum L2 Grant       $200K     2026-04-15  $150K    $50K     3.00

YOUR POSITIONS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Grant                    Position  Amount    Potential Win
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Solana DeFi Grant       YES       $5K       $5,952 (+19%)
Web3 Infrastructure     NO        $2K       $2,000 (0%)
Protocol Labs Storage   YES       $3K       $3,750 (+25%)

RESOLVED MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Grant                    Outcome   Pool      Winners   Your Win
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Avalanche Grant         ✅ YES    $80K      42        $2,380
Polygon zkEVM           ❌ NO     $60K      15        $0
Arbitrum Ecosystem      ✅ YES    $120K     67        $4,200

STATISTICS:
Total Markets: 8
Active: 5
Resolved: 3
Your Win Rate: 67% (2/3)
Total Profit: +$6,580
```

## Betting Strategy

```python
# grant_betting_strategy.py
class GrantBettingStrategy:
    def analyze_grant(self, grant):
        """Analyze grant approval probability"""
        score = 0
        
        # Organization reputation
        if grant['organization'] in ['Solana Foundation', 'Ethereum Foundation']:
            score += 30
        
        # Amount (smaller grants more likely)
        if grant['amount'] < 50000:
            score += 20
        elif grant['amount'] < 100000:
            score += 10
        
        # Focus area (hot topics)
        hot_topics = ['DeFi', 'ZK', 'AI', 'Infrastructure']
        if any(topic in grant['focus_area'] for topic in hot_topics):
            score += 25
        
        # Deadline (more time = better prep)
        days_until = (grant['deadline'] - now()).days
        if days_until > 60:
            score += 15
        elif days_until > 30:
            score += 10
        
        # Historical approval rate
        org_history = self.get_org_history(grant['organization'])
        score += org_history['approval_rate'] * 0.2
        
        return score  # 0-100
    
    def should_bet_yes(self, grant, market):
        """Decide if should bet YES"""
        score = self.analyze_grant(grant)
        implied_prob = market['yes_stake'] / (market['yes_stake'] + market['no_stake'])
        
        # Bet YES if our score > market probability
        return score > implied_prob * 100
    
    def calculate_bet_size(self, confidence, bankroll):
        """Kelly criterion for bet sizing"""
        edge = confidence - 0.5  # Edge over 50/50
        fraction = edge * 2  # Kelly fraction
        return bankroll * min(fraction, 0.25)  # Max 25% of bankroll
```

🏆💰 **Bet on grant approvals and profit!**
