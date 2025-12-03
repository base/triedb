mod handlers;
mod models;
mod state;

use axum::{
    http::Method,
    routing::get,
    Router,
};
use clap::Parser;
use include_dir::{include_dir, Dir};
use std::{net::SocketAddr, sync::Arc};
use tower_http::cors::{Any, CorsLayer};

use crate::state::AppState;

static FRONTEND_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/frontend/dist");

#[derive(Parser)]
#[command(name = "triedb-explorer")]
#[command(about = "Interactive web UI for exploring triedb")]
struct Args {
    /// Path to the database file
    #[arg(short, long)]
    database: String,

    /// Port to run the server on
    #[arg(short, long, default_value = "3000")]
    port: u16,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    println!("Opening database: {}", args.database);
    let state = Arc::new(
        AppState::new(&args.database).expect("Failed to open database"),
    );

    // CORS layer for development
    let cors = CorsLayer::new()
        .allow_methods([Method::GET, Method::POST])
        .allow_origin(Any)
        .allow_headers(Any);

    // API routes
    let api_routes = Router::new()
        .route("/root", get(handlers::pages::get_root))
        .route("/pages/:page_id", get(handlers::pages::get_page))
        .route("/pages/:page_id/info", get(handlers::pages::get_page_info))
        .route(
            "/pages/:page_id/descendants",
            get(handlers::pages::get_descendants),
        )
        .route(
            "/pages/:page_id/nodes/:cell_index/descendants",
            get(handlers::pages::get_node_descendants),
        )
        .route(
            "/nodes/:page_id/:cell_index",
            get(handlers::nodes::get_node),
        )
        .route("/search", get(handlers::search::search))
        .route("/metadata", get(handlers::metadata::get_metadata));

    // Main router
    let app = Router::new()
        .nest("/api", api_routes)
        .fallback(serve_frontend)
        .layer(cors)
        .with_state(state);

    let addr = SocketAddr::from(([127, 0, 0, 1], args.port));
    println!("Starting server at http://{}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

/// Serve static files from the embedded frontend directory.
async fn serve_frontend(uri: axum::http::Uri) -> impl axum::response::IntoResponse {
    let path = uri.path().trim_start_matches('/');
    let path = if path.is_empty() { "index.html" } else { path };

    match FRONTEND_DIR.get_file(path) {
        Some(file) => {
            let mime = mime_guess::from_path(path).first_or_octet_stream();
            (
                [(axum::http::header::CONTENT_TYPE, mime.as_ref())],
                file.contents(),
            )
                .into_response()
        }
        None => {
            // Fallback to index.html for SPA routing
            match FRONTEND_DIR.get_file("index.html") {
                Some(file) => (
                    [(axum::http::header::CONTENT_TYPE, "text/html")],
                    file.contents(),
                )
                    .into_response(),
                None => (
                    axum::http::StatusCode::NOT_FOUND,
                    "Frontend not found. Please build the frontend first.",
                )
                    .into_response(),
            }
        }
    }
}

use axum::response::IntoResponse;
