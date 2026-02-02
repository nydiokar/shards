use sha2::{Digest, Sha256};
use serde::{Deserialize, Serialize};

/// Harbot agent identity (rewrite of Python agent generation)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HarbotAgent {
    pub agent_name: String,
    pub shard_id: u8,
    pub identity_hash: String,
    pub capabilities: Vec<String>,
}

impl HarbotAgent {
    pub fn new(shard_id: u8) -> Self {
        let agent_name = format!("CICADA-Harbot-{}", shard_id);
        
        // Generate identity hash (equivalent to Python)
        let mut hasher = Sha256::new();
        hasher.update(agent_name.as_bytes());
        hasher.update(&[shard_id]);
        let identity_hash = hex::encode(hasher.finalize())[..16].to_string();
        
        Self {
            agent_name,
            shard_id,
            identity_hash,
            capabilities: vec![
                "hecke-eigenvalue-computation".to_string(),
                "maass-waveform-reconstruction".to_string(),
                "parquet-gossip".to_string(),
                "zk-witness-generation".to_string(),
                "morse-telegraph".to_string(),
                "tape-lifting".to_string(),
            ],
        }
    }
}

/// Generate all 71 agents (equivalent to Python loop)
pub fn generate_all_agents() -> Vec<HarbotAgent> {
    (0..71).map(HarbotAgent::new).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_agent_generation() {
        let agent = HarbotAgent::new(0);
        assert_eq!(agent.agent_name, "CICADA-Harbot-0");
        assert_eq!(agent.shard_id, 0);
        assert_eq!(agent.identity_hash.len(), 16);
        assert_eq!(agent.capabilities.len(), 6);
    }

    #[test]
    fn test_all_agents() {
        let agents = generate_all_agents();
        assert_eq!(agents.len(), 71);
        assert_eq!(agents[0].shard_id, 0);
        assert_eq!(agents[70].shard_id, 70);
    }
}
