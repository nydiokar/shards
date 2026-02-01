use anchor_lang::prelude::*;

declare_id!("Mon5terDAo111111111111111111111111111111111");

#[program]
pub mod monster_dao {
    use super::*;

    pub fn propose_subgroup(
        ctx: Context<ProposeSubgroup>,
        block: u64,
        subgroup: u8,
    ) -> Result<()> {
        let proposal = &mut ctx.accounts.proposal;
        proposal.block = block;
        proposal.subgroup = subgroup;
        proposal.votes_for = 0;
        proposal.votes_against = 0;
        proposal.approved = false;
        Ok(())
    }

    pub fn vote(ctx: Context<Vote>, approve: bool) -> Result<()> {
        let proposal = &mut ctx.accounts.proposal;
        let stake = ctx.accounts.voter.lamports();
        
        if approve {
            proposal.votes_for += stake;
        } else {
            proposal.votes_against += stake;
        }
        
        let total = proposal.votes_for + proposal.votes_against;
        if proposal.votes_for > total * 2 / 3 {
            proposal.approved = true;
            emit!(SubgroupApproved {
                block: proposal.block,
                subgroup: proposal.subgroup,
            });
        }
        Ok(())
    }
}

#[derive(Accounts)]
pub struct ProposeSubgroup<'info> {
    #[account(init, payer = proposer, space = 8 + 32)]
    pub proposal: Account<'info, Proposal>,
    #[account(mut)]
    pub proposer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct Vote<'info> {
    #[account(mut)]
    pub proposal: Account<'info, Proposal>,
    pub voter: Signer<'info>,
}

#[account]
pub struct Proposal {
    pub block: u64,
    pub subgroup: u8,
    pub votes_for: u64,
    pub votes_against: u64,
    pub approved: bool,
}

#[event]
pub struct SubgroupApproved {
    pub block: u64,
    pub subgroup: u8,
}
