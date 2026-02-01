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
        let voter = &ctx.accounts.voter;
        
        // Get voting power from reward balance
        let voting_power = get_reward_balance(voter.key())?;
        require!(voting_power > 0, ErrorCode::NoVotingPower);
        
        if approve {
            proposal.votes_for += voting_power;
        } else {
            proposal.votes_against += voting_power;
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

fn get_reward_balance(voter: Pubkey) -> Result<u64> {
    // Query reward balance from Ethereum ZK-rollup via bridge
    // For now, return mock value
    Ok(1000)
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
