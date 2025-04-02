use triedb::Database;
use std::env;
use std::fs::File;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Get the first command line argument
    let args: Vec<String> = env::args().collect();
    let file_path = args.get(1).ok_or("Usage: cargo run <db path> <page id>")?;
    let page_id_str = args.get(2).ok_or("Usage: cargo run <db path> <page id>")?;

    let db = match Database::open(file_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e)
    };

    let page_id: u32 = page_id_str.parse().unwrap();

    //KALEY TODO fix, maybe create/pass file_writer here instead
    let output_file = File::create("./printed_page")?;
    match db.pretty_print(&output_file, page_id) {
        Ok(_) => println!("Page printed to {}", file_path),
        Err(e) => println!("Error printing page: {:?}", e)
    }
    
    
    Ok(())
}

