# Open Source Investment Portfolio Markets

**Bet on companies meeting OSS investment criteria**

## Portfolio Criteria (from introspector-llc)

### Fitness Criteria
1. **Rule Abiding** - Clear rules, community guidelines
2. **Non-Discrimination** - Open to all contributors
3. **Documentation Quality** - Well-documented, reproducible
4. **Industry Standards** - Best practices alignment
5. **Governance** - Transparent decision-making
6. **Well-Supported** - Active community, prompt PR reviews
7. **Update Frequency** - Regular updates, security patches

### Engagement
- Active contributor engagement
- High retention, low turnover
- Detailed PR reviews
- Fair bug report handling

### Privacy & Freedom
- No mandatory tracking
- Self-hosting capable
- FLOSS commitment
- OSI-approved licenses

### Quality Systems
- Pre-commit hooks
- Testing procedures
- Failing test action
- Security best practices
- Reproducible builds

## Anchor Program

```rust
// programs/oss-portfolio/src/lib.rs
use anchor_lang::prelude::*;

declare_id!("OSSPoRtFoLioMaRkEtv111111111111111111111111");

#[program]
pub mod oss_portfolio {
    use super::*;

    pub fn create_company_market(
        ctx: Context<CreateCompanyMarket>,
        company_name: String,
        repo_url: String,
        criteria: Vec<Criterion>,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        market.company_name = company_name;
        market.repo_url = repo_url;
        market.criteria = criteria;
        market.total_score = 0;
        market.yes_stake = 0;
        market.no_stake = 0;
        market.resolved = false;
        Ok(())
    }

    pub fn score_criterion(
        ctx: Context<ScoreCriterion>,
        criterion_index: u8,
        score: u8, // 0-100
        evidence: String,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.criteria[criterion_index as usize].score = score;
        market.criteria[criterion_index as usize].evidence = evidence;
        
        // Recalculate total score
        market.total_score = market.calculate_total_score();
        
        emit!(CriterionScored {
            company: market.company_name.clone(),
            criterion: market.criteria[criterion_index as usize].name.clone(),
            score,
        });
        
        Ok(())
    }

    pub fn bet_investable(ctx: Context<Bet>, amount: u64) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        market.yes_stake += amount;
        Ok(())
    }

    pub fn bet_not_investable(ctx: Context<Bet>, amount: u64) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        market.no_stake += amount;
        Ok(())
    }

    pub fn resolve_market(
        ctx: Context<ResolveMarket>,
        investable: bool,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(!market.resolved, ErrorCode::MarketResolved);
        
        market.resolved = true;
        market.investable = Some(investable);
        
        emit!(CompanyEvaluated {
            company: market.company_name.clone(),
            total_score: market.total_score,
            investable,
        });
        
        Ok(())
    }
}

#[derive(Accounts)]
pub struct CreateCompanyMarket<'info> {
    #[account(
        init,
        payer = authority,
        space = 8 + CompanyMarket::LEN,
    )]
    pub market: Account<'info, CompanyMarket>,
    #[account(mut)]
    pub authority: Signer<'info>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct ScoreCriterion<'info> {
    #[account(mut)]
    pub market: Account<'info, CompanyMarket>,
    pub scorer: Signer<'info>,
}

#[derive(Accounts)]
pub struct Bet<'info> {
    #[account(mut)]
    pub market: Account<'info, CompanyMarket>,
    pub user: Signer<'info>,
}

#[derive(Accounts)]
pub struct ResolveMarket<'info> {
    #[account(mut)]
    pub market: Account<'info, CompanyMarket>,
    pub authority: Signer<'info>,
}

#[account]
pub struct CompanyMarket {
    pub company_name: String,
    pub repo_url: String,
    pub criteria: Vec<Criterion>,
    pub total_score: u16,
    pub yes_stake: u64,
    pub no_stake: u64,
    pub resolved: bool,
    pub investable: Option<bool>,
}

impl CompanyMarket {
    pub const LEN: usize = 64 + 128 + 1024 + 2 + 8 + 8 + 1 + 2;
    
    pub fn calculate_total_score(&self) -> u16 {
        let sum: u32 = self.criteria.iter().map(|c| c.score as u32).sum();
        let avg = sum / self.criteria.len() as u32;
        avg as u16
    }
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct Criterion {
    pub name: String,
    pub weight: u8,
    pub score: u8,
    pub evidence: String,
}

#[event]
pub struct CriterionScored {
    pub company: String,
    pub criterion: String,
    pub score: u8,
}

#[event]
pub struct CompanyEvaluated {
    pub company: String,
    pub total_score: u16,
    pub investable: bool,
}

#[error_code]
pub enum ErrorCode {
    #[msg("Market already resolved")]
    MarketResolved,
}
```

## Company Evaluator

```python
# oss_evaluator.py
import requests
from github import Github

class OSSEvaluator:
    def __init__(self, github_token):
        self.gh = Github(github_token)
    
    def evaluate_company(self, repo_url):
        """Evaluate company against OSS criteria"""
        repo = self.gh.get_repo(repo_url.replace('https://github.com/', ''))
        
        scores = {
            'rule_abiding': self.check_rules(repo),
            'non_discrimination': self.check_discrimination(repo),
            'documentation': self.check_documentation(repo),
            'governance': self.check_governance(repo),
            'well_supported': self.check_support(repo),
            'engagement': self.check_engagement(repo),
            'privacy': self.check_privacy(repo),
            'floss_commitment': self.check_floss(repo),
            'quality_systems': self.check_quality(repo),
            'security': self.check_security(repo),
            'reproducibility': self.check_reproducibility(repo),
        }
        
        total = sum(scores.values()) / len(scores)
        
        return {
            'repo': repo_url,
            'scores': scores,
            'total_score': total,
            'investable': total >= 70,  # 70% threshold
        }
    
    def check_rules(self, repo):
        """Check for CODE_OF_CONDUCT, CONTRIBUTING"""
        score = 0
        try:
            repo.get_contents("CODE_OF_CONDUCT.md")
            score += 50
        except:
            pass
        
        try:
            repo.get_contents("CONTRIBUTING.md")
            score += 50
        except:
            pass
        
        return score
    
    def check_documentation(self, repo):
        """Check documentation quality"""
        score = 0
        
        # README exists
        try:
            readme = repo.get_readme()
            if len(readme.decoded_content) > 1000:
                score += 30
        except:
            pass
        
        # Docs folder
        try:
            repo.get_contents("docs")
            score += 30
        except:
            pass
        
        # Wiki
        if repo.has_wiki:
            score += 20
        
        # GitHub Pages
        if repo.has_pages:
            score += 20
        
        return min(score, 100)
    
    def check_support(self, repo):
        """Check community support"""
        score = 0
        
        # Stars
        if repo.stargazers_count > 1000:
            score += 20
        elif repo.stargazers_count > 100:
            score += 10
        
        # Contributors
        contributors = repo.get_contributors().totalCount
        if contributors > 50:
            score += 20
        elif contributors > 10:
            score += 10
        
        # Open issues response time
        issues = repo.get_issues(state='closed')[:10]
        if issues:
            avg_time = sum((i.closed_at - i.created_at).days for i in issues) / len(issues)
            if avg_time < 7:
                score += 30
            elif avg_time < 30:
                score += 15
        
        # PR merge rate
        prs = repo.get_pulls(state='all')[:100]
        if prs:
            merged = sum(1 for pr in prs if pr.merged)
            merge_rate = merged / len(prs)
            score += int(merge_rate * 30)
        
        return min(score, 100)
    
    def check_floss(self, repo):
        """Check FLOSS commitment"""
        score = 0
        
        # OSI-approved license
        osi_licenses = ['MIT', 'Apache-2.0', 'GPL-3.0', 'BSD-3-Clause', 'AGPL-3.0']
        if repo.license and repo.license.spdx_id in osi_licenses:
            score += 50
        
        # No CLA required
        try:
            repo.get_contents("CLA.md")
            score -= 20  # Penalty for CLA
        except:
            score += 20
        
        # Foundation backing
        if 'foundation' in repo.description.lower():
            score += 30
        
        return max(min(score, 100), 0)
    
    def check_quality(self, repo):
        """Check quality systems"""
        score = 0
        
        # CI/CD
        try:
            repo.get_contents(".github/workflows")
            score += 40
        except:
            pass
        
        # Pre-commit hooks
        try:
            repo.get_contents(".pre-commit-config.yaml")
            score += 30
        except:
            pass
        
        # Tests
        try:
            repo.get_contents("tests")
            score += 30
        except:
            try:
                repo.get_contents("test")
                score += 30
            except:
                pass
        
        return min(score, 100)
```

## Dashboard

```
🏢 OPEN SOURCE INVESTMENT PORTFOLIO MARKETS 🏢

COMPANIES UNDER EVALUATION:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Company              Score   INVEST   NO      Odds    Status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Dioxus              85/100  $40K     $10K    4.00    ✅ Investable
Harbor P2P          78/100  $30K     $15K    2.00    ✅ Investable
Bisque HTTP         72/100  $25K     $20K    1.25    ✅ Investable
zkprologml          65/100  $15K     $25K    0.60    ❌ Not Yet
Escaped-RDFa        58/100  $10K     $30K    0.33    ❌ Not Yet

CRITERIA SCORES:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Company: Dioxus
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Rule Abiding:        95/100  ✅ CODE_OF_CONDUCT, CONTRIBUTING
Documentation:       90/100  ✅ Excellent docs, examples
Governance:          80/100  ✅ Transparent, community-driven
Well-Supported:      85/100  ✅ 15K stars, 200+ contributors
Engagement:          90/100  ✅ Fast PR reviews, active maintainers
Privacy:             80/100  ✅ No tracking, self-hostable
FLOSS Commitment:    95/100  ✅ MIT license, no CLA
Quality Systems:     85/100  ✅ CI/CD, pre-commit, tests
Security:            75/100  ✅ Security policy, audits
Reproducibility:     80/100  ✅ Nix flake, reproducible builds

TOTAL: 85/100 ✅ INVESTABLE

RED FLAGS DETECTED:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Company              Issue                    Severity
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
HashiCorp           License switch (BSL)     🔴 CRITICAL
LiteLLM             License switch           🔴 CRITICAL
OpenFaaS            License switch           🔴 CRITICAL
Redis               License switch (SSPL)    🔴 CRITICAL

PORTFOLIO ALLOCATION:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Category            Companies    Allocation   Score
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
UI Frameworks       3            $150K        82/100
P2P Networks        2            $100K        75/100
Security Tools      4            $200K        78/100
AI/ML Tools         2            $80K         68/100
Infrastructure      5            $250K        80/100

TOTAL PORTFOLIO: $780K
AVG SCORE: 77/100
```

🏢💰 **Bet on OSS companies meeting investment criteria!**
