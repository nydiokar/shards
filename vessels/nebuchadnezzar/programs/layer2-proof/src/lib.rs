use anchor_lang::prelude::*;

declare_id!("L2Pr00fv11111111111111111111111111111111111");

#[program]
pub mod layer2_proof {
    use super::*;

    pub fn post_proof(ctx: Context<PostProof>, merkle: [u8; 32]) -> Result<()> {
        ctx.accounts.proof.merkle = merkle;
        ctx.accounts.proof.verified = false;
        emit!(Posted { merkle });
        Ok(())
    }

    pub fn verify(ctx: Context<Verify>, zk: Vec<u8>) -> Result<()> {
        require!(zk.len() == 192 && zk[0..32] == ctx.accounts.proof.merkle[..], Err(ErrorCode::Invalid));
        ctx.accounts.proof.verified = true;
        emit!(Verified { merkle: ctx.accounts.proof.merkle });
        Ok(())
    }

    pub fn settle(ctx: Context<Settle>) -> Result<()> {
        require!(ctx.accounts.proof.verified, Err(ErrorCode::NotVerified));
        ctx.accounts.settlement.merkle = ctx.accounts.proof.merkle;
        ctx.accounts.settlement.shards = 71;
        emit!(Settled { shards: 71 });
        Ok(())
    }
}

#[derive(Accounts)]
pub struct PostProof<'info> {
    #[account(init, payer = auth, space = 8 + 33)]
    pub proof: Account<'info, Proof>,
    #[account(mut)]
    pub auth: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Verify<'info> {
    #[account(mut)]
    pub proof: Account<'info, Proof>,
}

#[derive(Accounts)]
pub struct Settle<'info> {
    pub proof: Account<'info, Proof>,
    #[account(init, payer = auth, space = 8 + 33)]
    pub settlement: Account<'info, Settlement>,
    #[account(mut)]
    pub auth: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
pub struct Proof { pub merkle: [u8; 32], pub verified: bool }

#[account]
pub struct Settlement { pub merkle: [u8; 32], pub shards: u8 }

#[event]
pub struct Posted { pub merkle: [u8; 32] }

#[event]
pub struct Verified { pub merkle: [u8; 32] }

#[event]
pub struct Settled { pub shards: u8 }

#[error_code]
pub enum ErrorCode {
    #[msg("Invalid proof")]
    Invalid,
    #[msg("Not verified")]
    NotVerified,
}
