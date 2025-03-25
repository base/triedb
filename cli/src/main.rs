use triedb::{Database, database::Error};
use std::env;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Get the first command line argument
    let args: Vec<String> = env::args().collect();
    let file_path = args.get(1).ok_or("Please provide a file path as an argument")?;

    let db = match Database::open(file_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e)
    };

    db.pretty_print();
    
    
    
    Ok(())
}

