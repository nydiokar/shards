// Multi-level review system with scholars and muses
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::process::Command;

#[derive(Debug, Serialize, Deserialize)]
struct Persona {
    focus: String,
    prompt: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct Review {
    persona: String,
    role: String,
    content: String,
}

fn scholars() -> HashMap<&'static str, Persona> {
    let mut map = HashMap::new();
    map.insert("mathematician", Persona {
        focus: "Mathematical rigor, proof correctness".to_string(),
        prompt: "Review for proof correctness and notation".to_string(),
    });
    map.insert("computer_scientist", Persona {
        focus: "Algorithmic complexity, implementation".to_string(),
        prompt: "Review for algorithm correctness".to_string(),
    });
    map.insert("group_theorist", Persona {
        focus: "Monster group properties".to_string(),
        prompt: "Review Monster group usage".to_string(),
    });
    map
}

fn muses() -> HashMap<&'static str, Persona> {
    let mut map = HashMap::new();
    map.insert("visionary", Persona {
        focus: "Big picture, connections".to_string(),
        prompt: "What profound patterns?".to_string(),
    });
    map.insert("storyteller", Persona {
        focus: "Narrative, accessibility".to_string(),
        prompt: "How to explain this?".to_string(),
    });
    map
}

fn review_with_persona(page_num: u32, persona_name: &str, persona: &Persona) -> String {
    let prompt = format!("Page {} - {}: {}", page_num, persona_name, persona.prompt);
    
    // Call ollama (simplified)
    let output = Command::new("curl")
        .args(&["-s", "http://localhost:11434/api/generate"])
        .output();
    
    match output {
        Ok(o) => String::from_utf8_lossy(&o.stdout).to_string(),
        Err(_) => "Error".to_string(),
    }
}

fn main() {
    println!("🎓 Multi-Level Review System");
    
    let scholars = scholars();
    let muses = muses();
    
    println!("Scholars: {}", scholars.len());
    println!("Muses: {}", muses.len());
}
