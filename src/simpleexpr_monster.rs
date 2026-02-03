use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
pub struct SimpleExprMonster {
    pub expr: String,
    pub fold: u8,
    pub prime: u64,
    pub brainfuck: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ConstValue {
    pub name: String,
    pub levels: Vec<String>,
    pub shard: u8,
    pub hecke: u64,
    pub godel: u64,
}

pub fn capture_const_values(json_path: &str) -> Result<Vec<ConstValue>, Box<dyn std::error::Error>> {
    let data = std::fs::read_to_string(json_path)?;
    let lean_expr: serde_json::Value = serde_json::from_str(&data)?;
    
    let mut consts = Vec::new();
    
    // Extract all const declarations
    if let Some(rules) = lean_expr.pointer("/cnstInf/Rules") {
        if let Some(arr) = rules.as_array() {
            for rule in arr {
                if let Some(name) = rule["name"].as_str() {
                    if name.contains("const") {
                        let godel = godel_encode(name);
                        let hecke = (godel % 15) as u64 + 2;
                        let shard = ((hecke * 3) % 71) as u8;
                        
                        consts.push(ConstValue {
                            name: name.to_string(),
                            levels: vec![],
                            shard,
                            hecke,
                            godel,
                        });
                    }
                }
            }
        }
    }
    
    Ok(consts)
}

fn godel_encode(s: &str) -> u64 {
    s.bytes().fold(0u64, |acc, b| (acc * 31 + b as u64) % 808017)
}

pub fn compile_simpleexpr(json_path: &str) -> Result<Vec<SimpleExprMonster>, Box<dyn std::error::Error>> {
    let data = std::fs::read_to_string(json_path)?;
    let lean_expr: serde_json::Value = serde_json::from_str(&data)?;
    
    let mapping = HashMap::from([
        ("bvar", ("BVAR", 1, 71, "+><")),
        ("sort", ("SORT", 0, 2, "++[>+<]")),
        ("const", ("CONST", 2, 47, "[>+<]")),
        ("app", ("APP", 3, 19, ">>+")),
        ("lam", ("LAM", 4, 17, "+++[>]")),
        ("forallE", ("FORALL", 5, 13, "++++[>>]")),
    ]);
    
    let mut result = Vec::new();
    
    if let Some(rules) = lean_expr.pointer("/cnstInf/Rules") {
        if let Some(arr) = rules.as_array() {
            for rule in arr {
                if let Some(name) = rule["name"].as_str() {
                    let key = name.split('.').last().unwrap_or("");
                    if let Some(&(expr, fold, prime, bf)) = mapping.get(key) {
                        result.push(SimpleExprMonster {
                            expr: expr.to_string(),
                            fold,
                            prime,
                            brainfuck: bf.to_string(),
                        });
                    }
                }
            }
        }
    }
    
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_const_capture() {
        let path = "/mnt/data1/nix/time/2025/08/07/ragit/vendor/meta-introspector/solfunmeme-dioxus/hg_datasets/microlean4/SimpleExpr.rec_686e510a6699f2e1ff1b216c16d94cd379ebeca00c030a79a3134adff699e06c.json";
        let consts = capture_const_values(path).unwrap();
        assert!(consts.len() > 0);
    }
}
