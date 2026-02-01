# IKEA Catalog Prediction Market

**Bet on IKEA product prices, availability, and catalog changes!**

## Market Types

### 1. Price Predictions
Predict future prices of IKEA products:
- BILLY bookcase: Current $79.99 → Predict next quarter
- KALLAX shelf: Current $89.99 → Predict next quarter
- POÄNG chair: Current $99.99 → Predict next quarter
- MALM bed frame: Current $179.99 → Predict next quarter

### 2. Availability Markets
Bet on stock status:
- Will BILLY be in stock at store X on date Y?
- Will LACK table be discontinued?
- Will new color variant launch?

### 3. Catalog Changes
Predict catalog updates:
- New products added per quarter
- Products discontinued per quarter
- Price changes (up/down/same)
- New collections launched

### 4. Assembly Time Markets
Bet on actual assembly times vs. IKEA estimates:
- BILLY: Estimated 30min → Actual?
- KALLAX: Estimated 45min → Actual?
- PAX wardrobe: Estimated 2hr → Actual?

### 5. Name Prediction Markets
Guess Swedish names for new products:
- New bookcase will be called: BJÖRK, SKOG, TRÄD?
- New chair will be called: STOL, SÄTE, VILA?

## Architecture

```rust
use anchor_lang::prelude::*;

declare_id!("1K3Av1111111111111111111111111111111111111111");

#[program]
pub mod ikea_market {
    use super::*;

    pub fn create_price_market(
        ctx: Context<CreateMarket>,
        product: String,
        current_price: u64,
        prediction_date: i64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        
        market.product = product;
        market.current_price = current_price;
        market.prediction_date = prediction_date;
        market.total_bets = 0;
        market.resolved = false;
        
        emit!(IkeaMarketCreated {
            product: market.product.clone(),
            current_price,
            prediction_date,
        });
        
        Ok(())
    }

    pub fn place_bet(
        ctx: Context<PlaceBet>,
        predicted_price: u64,
        amount: u64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        let bet = &mut ctx.accounts.bet;
        
        bet.bettor = ctx.accounts.bettor.key();
        bet.predicted_price = predicted_price;
        bet.amount = amount;
        bet.timestamp = Clock::get()?.unix_timestamp;
        
        market.total_bets += 1;
        
        // Transfer bet amount
        let ix = anchor_lang::solana_program::system_instruction::transfer(
            &ctx.accounts.bettor.key(),
            &market.key(),
            amount,
        );
        
        anchor_lang::solana_program::program::invoke(
            &ix,
            &[
                ctx.accounts.bettor.to_account_info(),
                market.to_account_info(),
            ],
        )?;
        
        emit!(BetPlaced {
            product: market.product.clone(),
            bettor: bet.bettor,
            predicted_price,
            amount,
        });
        
        Ok(())
    }

    pub fn resolve_market(
        ctx: Context<ResolveMarket>,
        actual_price: u64,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        
        require!(!market.resolved, ErrorCode::AlreadyResolved);
        require!(
            Clock::get()?.unix_timestamp >= market.prediction_date,
            ErrorCode::TooEarly
        );
        
        market.actual_price = actual_price;
        market.resolved = true;
        
        emit!(MarketResolved {
            product: market.product.clone(),
            predicted: market.current_price,
            actual: actual_price,
        });
        
        Ok(())
    }

    pub fn claim_winnings(ctx: Context<ClaimWinnings>) -> Result<()> {
        let market = &ctx.accounts.market;
        let bet = &ctx.accounts.bet;
        
        require!(market.resolved, ErrorCode::NotResolved);
        
        // Calculate accuracy
        let diff = if market.actual_price > bet.predicted_price {
            market.actual_price - bet.predicted_price
        } else {
            bet.predicted_price - market.actual_price
        };
        
        let accuracy = 100 - ((diff * 100) / market.actual_price.max(1));
        
        // Winner gets 2x if within 5%
        let winnings = if accuracy >= 95 {
            bet.amount * 2
        } else if accuracy >= 90 {
            bet.amount * 3 / 2
        } else {
            0
        };
        
        if winnings > 0 {
            **market.to_account_info().try_borrow_mut_lamports()? -= winnings;
            **ctx.accounts.bettor.try_borrow_mut_lamports()? += winnings;
        }
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct CreateMarket<'info> {
    #[account(init, payer = authority, space = 8 + IkeaMarket::LEN)]
    pub market: Account<'info, IkeaMarket>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct PlaceBet<'info> {
    #[account(mut)]
    pub market: Account<'info, IkeaMarket>,
    #[account(init, payer = bettor, space = 8 + IkeaBet::LEN)]
    pub bet: Account<'info, IkeaBet>,
    #[account(mut)]
    pub bettor: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct ResolveMarket<'info> {
    #[account(mut)]
    pub market: Account<'info, IkeaMarket>,
}

#[derive(Accounts)]
pub struct ClaimWinnings<'info> {
    #[account(mut)]
    pub market: Account<'info, IkeaMarket>,
    pub bet: Account<'info, IkeaBet>,
    #[account(mut)]
    pub bettor: Signer<'info>,
}

#[account]
pub struct IkeaMarket {
    pub product: String,
    pub current_price: u64,
    pub actual_price: u64,
    pub prediction_date: i64,
    pub total_bets: u32,
    pub resolved: bool,
}

impl IkeaMarket {
    pub const LEN: usize = 64 + 8 + 8 + 8 + 4 + 1;
}

#[account]
pub struct IkeaBet {
    pub bettor: Pubkey,
    pub predicted_price: u64,
    pub amount: u64,
    pub timestamp: i64,
}

impl IkeaBet {
    pub const LEN: usize = 32 + 8 + 8 + 8;
}

#[event]
pub struct IkeaMarketCreated {
    pub product: String,
    pub current_price: u64,
    pub prediction_date: i64,
}

#[event]
pub struct BetPlaced {
    pub product: String,
    pub bettor: Pubkey,
    pub predicted_price: u64,
    pub amount: u64,
}

#[event]
pub struct MarketResolved {
    pub product: String,
    pub predicted: u64,
    pub actual: u64,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Market already resolved")]
    AlreadyResolved,
    #[msg("Too early to resolve")]
    TooEarly,
    #[msg("Market not resolved")]
    NotResolved,
}
```

## Dashboard

```
🛋️ IKEA CATALOG PREDICTION MARKET 🛋️

ACTIVE MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Product         Current    Avg Prediction  Bets  Resolve Date
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
BILLY bookcase  $79.99     $82.50         42    2026-04-01
KALLAX shelf    $89.99     $87.25         71    2026-04-01
POÄNG chair     $99.99     $104.99        137   2026-04-01
MALM bed        $179.99    $184.50        263   2026-04-01

ASSEMBLY TIME MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Product         IKEA Est   Avg Prediction  Bets
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
BILLY           30min      45min          89
KALLAX          45min      60min          67
PAX wardrobe    2hr        3.5hr          124

AVAILABILITY MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Question                                    Yes    No     Total
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
BILLY in stock NYC 2026-03-01?             65%    35%    42 bets
LACK discontinued by Q2?                   30%    70%    28 bets
New BILLY color variant Q1?                55%    45%    37 bets

NAME PREDICTION MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
New bookcase name:
  BJÖRK:  35% (14 bets)
  SKOG:   40% (16 bets)
  TRÄD:   25% (10 bets)

RESOLVED MARKETS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Product         Predicted  Actual   Winner          Payout
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
HEMNES dresser  $249.99    $249.99  @ikea_oracle    2x ✅
EKTORP sofa     $599.99    $649.99  @furniture_pro  1.5x ✅

LEADERBOARD:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Rank  User              Wins  Accuracy  Total Won
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1     @ikea_oracle      12    96%       8.4 SOL
2     @furniture_pro    10    94%       6.2 SOL
3     @swedish_expert   8     92%       4.8 SOL

STATISTICS:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Total Markets: 42
Active Bets: 1,247
Total Volume: 71 SOL
Avg Accuracy: 89%

BET ON:
- Price changes
- Assembly times
- Stock availability
- Product names
- Catalog updates
- Discontinuations
```

## Integration with CICADA-71

**Shard 72 (if we had it): IKEA Market**
- Real-world consumer goods
- Swedish naming conventions
- Assembly complexity
- Supply chain predictions

**Data Sources:**
- IKEA API (prices, availability)
- Web scraping (catalog changes)
- User submissions (assembly times)
- Social media (rumors, leaks)

🛋️⚡ **Bet on Swedish furniture! Predict the flat-pack future!** ✨
