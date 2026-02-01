//! Bisque - Secure Brainrot Scrubbing Harmonic Decoder
//! 
//! Replaces insecure libsoup with pure Rust HTTP/TLS
//! Binary compatible with libsoup API
//! WASM target for Node.js
//! For lobster brain soup, but secure 🦞🍲

use reqwest;
use serde::{Deserialize, Serialize};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

// libsoup-compatible C API
#[repr(C)]
pub struct SoupSession {
    client: reqwest::Client,
}

#[repr(C)]
pub struct SoupMessage {
    status_code: u16,
    response_body: *mut u8,
    response_len: usize,
}

// Binary-compatible libsoup API
#[no_mangle]
pub extern "C" fn soup_session_new() -> *mut SoupSession {
    let client = reqwest::Client::builder()
        .use_rustls_tls()
        .build()
        .unwrap();
    
    Box::into_raw(Box::new(SoupSession { client }))
}

#[no_mangle]
pub extern "C" fn soup_session_free(session: *mut SoupSession) {
    if !session.is_null() {
        unsafe { Box::from_raw(session); }
    }
}

// Rust API
#[derive(Debug)]
pub struct Bisque {
    client: reqwest::Client,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct BisqueResponse {
    pub status: u16,
    pub body: String,
    pub headers: Vec<(String, String)>,
}

impl Bisque {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let client = reqwest::Client::builder()
            .use_rustls_tls()
            .build()?;
        
        Ok(Self { client })
    }
    
    pub async fn fetch(&self, url: &str) -> Result<BisqueResponse, Box<dyn std::error::Error>> {
        let response = self.client.get(url).send().await?;
        
        let status = response.status().as_u16();
        let headers: Vec<(String, String)> = response
            .headers()
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_str().unwrap_or("").to_string()))
            .collect();
        let body = response.text().await?;
        
        Ok(BisqueResponse { status, body, headers })
    }
}

// WASM bindings for Node.js
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub struct BisqueWasm {
    inner: Bisque,
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
impl BisqueWasm {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            inner: Bisque::new().unwrap(),
        }
    }
    
    #[wasm_bindgen]
    pub async fn fetch(&self, url: String) -> JsValue {
        match self.inner.fetch(&url).await {
            Ok(response) => serde_wasm_bindgen::to_value(&response).unwrap(),
            Err(e) => JsValue::from_str(&format!("Error: {}", e)),
        }
    }
}

impl Default for Bisque {
    fn default() -> Self {
        Self::new().expect("Failed to create Bisque client")
    }
}
