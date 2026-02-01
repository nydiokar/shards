use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum MonsterSubgroup {
    BabyMonster,      // 2.B
    Fischer24,        // Fi₂₄'
    Conway1,          // Co₁
    Thompson,         // Th
    PSL2_71,          // PSL₂(71)
    Prime71,          // 71:70
}

impl MonsterSubgroup {
    pub fn order(&self) -> u128 {
        match self {
            Self::BabyMonster => 4_154_781_481_226_426_191_177_580_544_000_000,
            Self::Fischer24 => 1_255_205_709_190_661_721_292_800,
            Self::Conway1 => 4_157_776_806_543_360_000,
            Self::Thompson => 90_745_943_887_872_000,
            Self::PSL2_71 => 178_920, // (71³-71)/2
            Self::Prime71 => 71,
        }
    }
    
    pub fn for_layer(layer: u8) -> Self {
        match layer % 6 {
            0 => Self::BabyMonster,
            1 => Self::Fischer24,
            2 => Self::Conway1,
            3 => Self::Thompson,
            4 => Self::PSL2_71,
            _ => Self::Prime71,
        }
    }
}

pub fn derive_seed(subgroup: MonsterSubgroup, block: u64) -> u128 {
    (subgroup.order() ^ (block as u128)) % (1u128 << 64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_71_layers() {
        for layer in 0..71 {
            let sg = MonsterSubgroup::for_layer(layer);
            assert!(sg.order() > 0);
        }
    }
    
    #[test]
    fn test_psl2_71_order() {
        let sg = MonsterSubgroup::PSL2_71;
        assert_eq!(sg.order(), 178_920);
    }
}
