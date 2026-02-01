use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ShardResource {
    pub shard_id: u8,
    pub cpu_cores: Vec<usize>,
    pub ram_gb: f32,
    pub disk_path: String,
    pub priority: u8,
}

impl ShardResource {
    pub fn allocate(shard_id: u8) -> Self {
        match shard_id {
            0..=22 => Self {
                shard_id,
                cpu_cores: vec![shard_id as usize],
                ram_gb: 1.0,
                disk_path: if shard_id % 2 == 0 { "/nix/store".into() } else { "target/".into() },
                priority: 1,
            },
            23..=45 => {
                let base = (shard_id - 23) * 2;
                Self {
                    shard_id,
                    cpu_cores: vec![base as usize % 23, (base + 1) as usize % 23],
                    ram_gb: 2.0,
                    disk_path: "/nix/store".into(),
                    priority: 2,
                }
            },
            46..=57 => {
                let base = (shard_id - 46) * 4;
                Self {
                    shard_id,
                    cpu_cores: (base..base + 4).map(|i| (i % 23) as usize).collect(),
                    ram_gb: 4.0,
                    disk_path: "mixed".into(),
                    priority: 3,
                }
            },
            58..=70 => Self {
                shard_id,
                cpu_cores: (0..23).collect(),
                ram_gb: 23.0,
                disk_path: "all".into(),
                priority: 4,
            },
            _ => unreachable!(),
        }
    }

    pub fn affinity_mask(&self) -> String {
        self.cpu_cores.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",")
    }
}

pub fn prime_encode(cpu: usize, gpu: usize, ram: usize, disk: usize) -> u8 {
    ((2 * cpu + 3 * gpu + 5 * ram + 7 * disk) % 71) as u8
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_shards_allocated() {
        for shard in 0..71 {
            let res = ShardResource::allocate(shard);
            assert_eq!(res.shard_id, shard);
            assert!(!res.cpu_cores.is_empty());
            assert!(res.ram_gb > 0.0);
        }
    }

    #[test]
    fn test_prime_factorization() {
        assert_eq!(2 * 3 * 5 * 7, 210);
        assert_eq!(prime_encode(1, 0, 0, 0), 2);
        assert_eq!(prime_encode(0, 1, 0, 0), 3);
        assert_eq!(prime_encode(0, 0, 1, 0), 5);
        assert_eq!(prime_encode(0, 0, 0, 1), 7);
    }
}
