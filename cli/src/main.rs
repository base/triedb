use clap::{Parser, Subcommand};
use triedb::Database;
use std::fs::File;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Print a specific page from the database
    Print {
        /// Path to the database file
        #[arg(short = 'd', long = "database")]
        path: String,
        
        /// Page ID to print (optional)
        #[arg(short = 'p', long = "page")]
        page_id: Option<u32>,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output", default_value="./printed_page")]
        output_path: String, 
    },
    
    // Get information about a specific account
    // Account {
    //     // Path to the database file
    //     #[arg(short, long)]
    //     path: String,
        
    //     // Account ID to look up
    //     #[arg(short, long)]
    //     account_id: String,
    // },
    
    // // Get statistics about the database
    // Stats {
    //     // Path to the database file
    //     #[arg(short, long)]
    //     path: String,
    // },
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();
    
    match args.command {
        Commands::Print { path, page_id, output_path } => {
            print_page(&path, page_id, &output_path);
        }
        // Commands::Account { path, account_id } => {
        //     get_account(&path, &account_id)?;
        // }
        // Commands::Stats { path } => {
        //     get_stats(&path)?;
        // }
    }
    
    Ok(())
}

fn print_page(db_path: &str, page_id: Option<u32>, output_path: &str) {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };

    let output_file = File::create(output_path).unwrap();
    match db.print_page(&output_file, page_id) {
        Ok(_) => println!("Page printed to {}", output_path),
        Err(e) => println!("Error printing page: {:?}", e),
    }
}

// fn get_account(db_path: &str, account_id: &str) -> Result<(), Box<dyn std::error::Error>> {
//     let db = Database::open(db_path)?;
//     let mut context = db.start_read_only_transaction()?;
//     // TODO: Implement account lookup
//     println!("Looking up account: {}", account_id);
//     Ok(())
// }

// fn get_stats(db_path: &str) -> Result<(), Box<dyn std::error::Error>> {
//     let db = Database::open(db_path)?;
//     let mut context = db.start_read_only_transaction()?;
//     // TODO: Implement stats collection
//     println!("Getting database statistics");
//     Ok(())
// }
