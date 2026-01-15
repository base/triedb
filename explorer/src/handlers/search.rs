use alloy_primitives::{hex, Address, StorageKey};
use alloy_trie::Nibbles;
use axum::{
    extract::{Query, State},
    Json,
};
use serde::Deserialize;
use std::sync::Arc;
use triedb::storage::explorer::PathSearchResult;

use crate::{models::ApiResponse, state::AppState};

#[derive(Debug, Deserialize)]
pub struct SearchQuery {
    /// The search query (path in hex, address, or storage slot)
    pub q: String,
    /// Type of query: "raw", "address", or "storage"
    #[serde(rename = "type", default = "default_query_type")]
    pub query_type: String,
}

fn default_query_type() -> String {
    "raw".to_string()
}

/// GET /api/search?q=<path>&type=<raw|address|storage>
pub async fn search(
    State(state): State<Arc<AppState>>,
    Query(params): Query<SearchQuery>,
) -> Json<ApiResponse<Option<PathSearchResult>>> {
    let result = parse_search_query(&params.q, &params.query_type);

    let nibbles = match result {
        Ok(n) => n,
        Err(e) => return Json(ApiResponse::error(e)),
    };

    let search_result = state.with_explorer(|explorer, context| {
        explorer
            .search_by_path(context, &nibbles)
            .map_err(|e| format!("Search failed: {}", e))
    });

    match search_result {
        Ok(data) => Json(ApiResponse::success(data)),
        Err(e) => Json(ApiResponse::error(e)),
    }
}

fn parse_search_query(query: &str, query_type: &str) -> Result<Nibbles, String> {
    match query_type {
        "raw" => {
            // Raw nibbles path (hex encoded)
            // Supports colon-separated format: "0xAccountPath:0xStoragePath" for account+storage paths
            let hex_str = query.strip_prefix("0x").unwrap_or(query);

            if let Some(colon_pos) = hex_str.find(':') {
                // Account + storage path format
                let account_hex = &hex_str[..colon_pos];
                let storage_hex = hex_str[colon_pos + 1..]
                    .strip_prefix("0x")
                    .unwrap_or(&hex_str[colon_pos + 1..]);

                // Combine account and storage nibbles
                let combined_hex = format!("{}{}", account_hex, storage_hex);
                let bytes =
                    hex::decode(&combined_hex).map_err(|e| format!("Invalid hex: {}", e))?;
                Ok(Nibbles::unpack(&bytes))
            } else {
                // Simple path
                let bytes = hex::decode(hex_str).map_err(|e| format!("Invalid hex: {}", e))?;
                Ok(Nibbles::unpack(&bytes))
            }
        }
        "address" => {
            // Ethereum address -> keccak256 hash -> nibbles
            let hex_str = query.strip_prefix("0x").unwrap_or(query);
            if hex_str.len() != 40 {
                return Err("Address must be 20 bytes (40 hex chars)".to_string());
            }
            let bytes: [u8; 20] = hex::decode(hex_str)
                .map_err(|e| format!("Invalid hex: {}", e))?
                .try_into()
                .map_err(|_| "Invalid address length".to_string())?;
            let address = Address::from(bytes);
            let hash = alloy_primitives::keccak256(address);
            Ok(Nibbles::unpack(hash))
        }
        "storage" => {
            // Format: "address:slot" or "address slot"
            let parts: Vec<&str> = query.split(|c| c == ':' || c == ' ').collect();
            if parts.len() != 2 {
                return Err(
                    "Storage query must be 'address:slot' or 'address slot'".to_string()
                );
            }

            let address_hex = parts[0].strip_prefix("0x").unwrap_or(parts[0]);
            if address_hex.len() != 40 {
                return Err("Address must be 20 bytes (40 hex chars)".to_string());
            }
            let address_bytes: [u8; 20] = hex::decode(address_hex)
                .map_err(|e| format!("Invalid address hex: {}", e))?
                .try_into()
                .map_err(|_| "Invalid address length".to_string())?;
            let address = Address::from(address_bytes);

            let slot_hex = parts[1].strip_prefix("0x").unwrap_or(parts[1]);
            let slot_bytes = hex::decode(slot_hex).map_err(|e| format!("Invalid slot hex: {}", e))?;
            let slot = StorageKey::left_padding_from(&slot_bytes);

            // Hash address and slot
            let address_hash = alloy_primitives::keccak256(address);
            let slot_hash = alloy_primitives::keccak256(slot);

            // Combine into 128 nibbles (64 for address hash + 64 for slot hash)
            let mut combined = Vec::with_capacity(64);
            combined.extend_from_slice(address_hash.as_slice());
            combined.extend_from_slice(slot_hash.as_slice());
            Ok(Nibbles::unpack(&combined))
        }
        _ => Err(format!("Unknown query type: {}", query_type)),
    }
}
