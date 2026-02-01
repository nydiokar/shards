// programs/self-lifting/src/lib.rs
use anchor_lang::prelude::*;

declare_id!("SeLfLiFtv1111111111111111111111111111111111");

#[program]
pub mod self_lifting {
    use super::*;

    pub fn lift(ctx: Context<Lift>) -> Result<()> {
        let old = &ctx.accounts.old_state;
        let new = &mut ctx.accounts.new_state;
        
        new.generation = old.generation + 1;
        new.previous = Some(old.key());
        new.next_seed = (new.generation % 71) as u8;
        
        emit!(Lifted {
            gen: new.generation,
            from: old.key(),
            to: new.key(),
        });
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct Lift<'info> {
    pub old_state: Account<'info, State>,
    #[account(init, payer = auth, space = 8 + 41, seeds = [b"state", &[old_state.next_seed]], bump)]
    pub new_state: Account<'info, State>,
    #[account(mut)]
    pub auth: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[account]
pub struct State {
    pub generation: u64,
    pub previous: Option<Pubkey>,
    pub next_seed: u8,
}

#[event]
pub struct Lifted {
    pub gen: u64,
    pub from: Pubkey,
    pub to: Pubkey,
}
