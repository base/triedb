use axum::{
    extract::{Path, State},
    Json,
};
use std::sync::Arc;
use triedb::page::PageId;

use crate::{
    models::{ApiResponse, DescendantsResponse, PageResponse, RootResponse},
    state::AppState,
};

/// GET /api/root - Get root page info and nodes
pub async fn get_root(
    State(state): State<Arc<AppState>>,
) -> Json<ApiResponse<RootResponse>> {
    let result = state.with_explorer(|explorer, context| {
        let root_page_id = explorer.get_root_page_id();

        match root_page_id {
            Some(page_id) => {
                let info = explorer.get_page_info(context, page_id);
                let nodes = explorer.get_page_nodes(context, page_id);

                match (info, nodes) {
                    (Ok(info), Ok(nodes)) => Ok(RootResponse {
                        root_page_id: Some(page_id.as_u32()),
                        page: Some(PageResponse { info, nodes }),
                    }),
                    (Err(e), _) => Err(format!("Failed to get page info: {}", e)),
                    (_, Err(e)) => Err(format!("Failed to get page nodes: {}", e)),
                }
            }
            None => Ok(RootResponse {
                root_page_id: None,
                page: None,
            }),
        }
    });

    match result {
        Ok(data) => Json(ApiResponse::success(data)),
        Err(e) => Json(ApiResponse::error(e)),
    }
}

/// GET /api/pages/:page_id - Get all nodes on a page with page info
pub async fn get_page(
    State(state): State<Arc<AppState>>,
    Path(page_id): Path<u32>,
) -> Json<ApiResponse<PageResponse>> {
    let result = state.with_explorer(|explorer, context| {
        let page_id = PageId::new(page_id).ok_or_else(|| "Invalid page ID".to_string())?;
        let info = explorer
            .get_page_info(context, page_id)
            .map_err(|e| format!("Failed to get page info: {}", e))?;
        let nodes = explorer
            .get_page_nodes(context, page_id)
            .map_err(|e| format!("Failed to get page nodes: {}", e))?;
        Ok(PageResponse { info, nodes })
    });

    match result {
        Ok(data) => Json(ApiResponse::success(data)),
        Err(e) => Json(ApiResponse::error(e)),
    }
}

/// GET /api/pages/:page_id/info - Get page metadata only
pub async fn get_page_info(
    State(state): State<Arc<AppState>>,
    Path(page_id): Path<u32>,
) -> Json<ApiResponse<triedb::storage::explorer::PageInfo>> {
    let result = state.with_explorer(|explorer, context| {
        let page_id = PageId::new(page_id).ok_or_else(|| "Invalid page ID".to_string())?;
        explorer
            .get_page_info(context, page_id)
            .map_err(|e| format!("Failed to get page info: {}", e))
    });

    match result {
        Ok(data) => Json(ApiResponse::success(data)),
        Err(e) => Json(ApiResponse::error(e)),
    }
}

/// GET /api/pages/:page_id/descendants - Get page-local descendants from cell 0
pub async fn get_descendants(
    State(state): State<Arc<AppState>>,
    Path(page_id): Path<u32>,
) -> Json<ApiResponse<DescendantsResponse>> {
    let result = state.with_explorer(|explorer, context| {
        let page_id = PageId::new(page_id).ok_or_else(|| "Invalid page ID".to_string())?;
        let nodes = explorer
            .walk_page_local_descendants(context, page_id, 0)
            .map_err(|e| format!("Failed to walk descendants: {}", e))?;
        Ok(DescendantsResponse {
            page_id: page_id.as_u32(),
            nodes,
        })
    });

    match result {
        Ok(data) => Json(ApiResponse::success(data)),
        Err(e) => Json(ApiResponse::error(e)),
    }
}

/// GET /api/pages/:page_id/nodes/:cell_index/descendants - Get descendants from specific node
pub async fn get_node_descendants(
    State(state): State<Arc<AppState>>,
    Path((page_id, cell_index)): Path<(u32, u8)>,
) -> Json<ApiResponse<DescendantsResponse>> {
    let result = state.with_explorer(|explorer, context| {
        let page_id = PageId::new(page_id).ok_or_else(|| "Invalid page ID".to_string())?;
        let nodes = explorer
            .walk_page_local_descendants(context, page_id, cell_index)
            .map_err(|e| format!("Failed to walk descendants: {}", e))?;
        Ok(DescendantsResponse {
            page_id: page_id.as_u32(),
            nodes,
        })
    });

    match result {
        Ok(data) => Json(ApiResponse::success(data)),
        Err(e) => Json(ApiResponse::error(e)),
    }
}
