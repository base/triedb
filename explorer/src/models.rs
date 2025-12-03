use serde::Serialize;
use triedb::storage::explorer::{ExplorerNode, PageInfo};

/// API response wrapper.
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ApiResponse<T: Serialize> {
    pub success: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<T>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

impl<T: Serialize> ApiResponse<T> {
    pub fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
        }
    }

    pub fn error(message: String) -> Self {
        Self {
            success: false,
            data: None,
            error: Some(message),
        }
    }
}

/// Response for page endpoints.
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PageResponse {
    pub info: PageInfo,
    pub nodes: Vec<ExplorerNode>,
}

/// Response for root endpoint.
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RootResponse {
    pub root_page_id: Option<u32>,
    pub page: Option<PageResponse>,
}

/// Response for descendants endpoint.
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DescendantsResponse {
    pub page_id: u32,
    pub nodes: Vec<ExplorerNode>,
}
