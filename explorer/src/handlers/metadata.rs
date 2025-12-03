use axum::{extract::State, Json};
use std::sync::Arc;
use triedb::storage::explorer::DatabaseInfo;

use crate::{models::ApiResponse, state::AppState};

/// GET /api/metadata - Get database metadata including orphaned pages
pub async fn get_metadata(
    State(state): State<Arc<AppState>>,
) -> Json<ApiResponse<DatabaseInfo>> {
    let data = state.with_explorer(|explorer, _context| explorer.get_database_info());
    Json(ApiResponse::success(data))
}
