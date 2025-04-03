use triedb::Database;
use std::env;
use std::fs::File;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Get the first command line argument
    let args: Vec<String> = env::args().collect();
    let command = args.get(1).ok_or("Usage: cargo run print <db path> <page id>")?.as_str();
    match command{
        "print" => {
            let db_path = args.get(2).ok_or("Usage: cargo run print <db path> <page id>")?;
            let page_id_str = args.get(3);
            let page_id = if page_id_str.is_none() {
                None
            } else {
                Some(page_id_str.unwrap().parse::<u32>()?)
            };
            
            let output_path = "./printed_page";
            print_page(db_path, page_id, output_path);
        }
        _ => println!("Usage: cargo run print <db path> <page id> ")
    }
    
    Ok(())
}

fn print_page(db_path: &str, page_id: Option<u32>, output_path: &str) {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e)
    };

    

    //KALEY TODO fix, maybe create/pass file_writer here instead
    let output_file = File::create(output_path).unwrap();
    match db.pretty_print(&output_file, page_id) {
        Ok(_) => println!("Page printed to {}", output_path),
        Err(e) => println!("Error printing page: {:?}", e)
    }

}

