use axum::{
    extract::{Path, State},
    Json,
};
use std::sync::Arc;
use triedb::{page::PageId, storage::explorer::ExplorerNode};

use crate::{models::ApiResponse, state::AppState};

/// GET /api/nodes/:page_id/:cell_index - Get a single node
pub async fn get_node(
    State(state): State<Arc<AppState>>,
    Path((page_id, cell_index)): Path<(u32, u8)>,
) -> Json<ApiResponse<ExplorerNode>> {
    let result = state.with_explorer(|explorer, context| {
        let page_id = PageId::new(page_id).ok_or_else(|| "Invalid page ID".to_string())?;
        explorer
            .get_node_at(context, page_id, cell_index)
            .map_err(|e| format!("Failed to get node: {}", e))
    });

    match result {
        Ok(data) => Json(ApiResponse::success(data)),
        Err(e) => Json(ApiResponse::error(e)),
    }
}
