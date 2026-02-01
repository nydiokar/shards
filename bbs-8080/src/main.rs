// 8080 BBS Server - 16-bit Address Bus Architecture
// Intel 8080 tribute: 8-bit data, 16-bit address, 64KB memory

use axum::{
    routing::{get, post},
    Router, Json,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;

// Intel 8080: 16-bit address bus (0x0000 - 0xFFFF = 64 KB)
const ADDRESS_SPACE: u16 = 0xFFFF;
const MEMORY_SIZE: usize = 65536; // 64 KB
const PORT: u16 = 8080;

// 7 registers (like Intel 8080: A, B, C, D, E, H, L)
const NUM_REGISTERS: usize = 7;

// Power-by-power memory layout (16-bit address bus)
const POWER_16_3: u16 = 0x1000; // 4096 (16³)
const POWER_16_2: u16 = 0x0100; // 256 (16²)
const POWER_16_1: u16 = 0x0010; // 16 (16¹)
const POWER_16_0: u16 = 0x0001; // 1 (16⁰)

// Memory regions
#[derive(Debug, Clone, Serialize, Deserialize)]
struct MemoryRegion {
    start: u16,
    end: u16,
    name: String,
    power: u8,
}

// 8080 Architecture
struct Architecture8080 {
    regions: Vec<MemoryRegion>,
}

impl Architecture8080 {
    fn new() -> Self {
        Self {
            regions: vec![
                MemoryRegion {
                    start: 0x0000,
                    end: 0x0FFF,
                    name: "Shard Storage (16⁰ region)".to_string(),
                    power: 0,
                },
                MemoryRegion {
                    start: 0x1000,
                    end: 0x1FFF,
                    name: "Agent Memory (16³ region)".to_string(),
                    power: 3,
                },
                MemoryRegion {
                    start: 0x2000,
                    end: 0x2FFF,
                    name: "Message Queue (16² region)".to_string(),
                    power: 2,
                },
                MemoryRegion {
                    start: 0x3000,
                    end: 0x3FFF,
                    name: "Emoji Cache (16¹ region)".to_string(),
                    power: 1,
                },
            ],
        }
    }
    
    fn route_to_shard(&self, addr: u16) -> u8 {
        (addr % 71) as u8
    }
}

// BBS Message
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Message {
    id: u16,
    shard: u8,
    content: String,
    emoji: String,
}

// API Handlers
async fn root() -> &'static str {
    "🔮⚡ 8080 BBS Server - 16-bit Perfect Architecture"
}

async fn architecture() -> Json<Vec<MemoryRegion>> {
    let arch = Architecture8080::new();
    Json(arch.regions)
}

async fn post_message(Json(msg): Json<Message>) -> Json<Message> {
    let arch = Architecture8080::new();
    let shard = arch.route_to_shard(msg.id);
    
    Json(Message {
        shard,
        ..msg
    })
}

async fn get_shard(axum::extract::Path(shard_id): axum::extract::Path<u8>) -> Json<String> {
    if shard_id > 71 {
        Json(format!("🚨 Shard {} is in jail! (sus)", shard_id))
    } else {
        Json(format!("🔮 Shard {} ready", shard_id))
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(root))
        .route("/architecture", get(architecture))
        .route("/message", post(post_message))
        .route("/shard/:id", get(get_shard));

    let addr = SocketAddr::from(([127, 0, 0, 1], PORT));
    
    println!("🔮⚡ 8080 BBS Server Starting");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("Intel 8080 Tribute:");
    println!("  8-bit data bus");
    println!("  16-bit address bus (64 KB memory)");
    println!("  2 MHz clock speed");
    println!("  7 registers (A, B, C, D, E, H, L)");
    println!("  Von Neumann architecture");
    println!("");
    println!("Server:");
    println!("  Port: {}", PORT);
    println!("  Address Space: 0x0000 - 0x{:04X}", ADDRESS_SPACE);
    println!("  Memory: {} KB", MEMORY_SIZE / 1024);
    println!("  Shards: 71 (mod 71 routing)");
    println!("");
    println!("Memory Layout:");
    println!("  0x0000-0x0FFF: Shard Storage (16⁰)");
    println!("  0x1000-0x1FFF: Agent Memory (16³)");
    println!("  0x2000-0x2FFF: Message Queue (16²)");
    println!("  0x3000-0x3FFF: Emoji Cache (16¹)");
    println!("");
    println!("Endpoints:");
    println!("  GET  /");
    println!("  GET  /architecture");
    println!("  POST /message");
    println!("  GET  /shard/:id");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("Listening on http://{}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
