use clap::{Parser, Subcommand};
use alloy_trie::Nibbles;
use std::fs::File;
use triedb::Database;

#[derive(Debug)]
enum AccountIdentifier {
    FullHash(String),                // 0x + 64 or 128 chars
    Address(String),                 // 0x + 40 chars
    AddressWithSlot(String, String), // 0x + 40 chars + 0x + variable length
}

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
        db_path: String,

        /// Page ID to print (optional)
        #[arg(short = 'p', long = "page")]
        page_id: Option<u32>,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output", default_value = "./printed_page")]
        output_path: String,
    },

    /// Get information about a specific account
    Account {
        /// Path to the database file
        #[arg(short = 'd', long = "database")]
        db_path: String,

        /// Account identifier in one of these formats:
        /// 1. Full hash (0x + 64 or 128 hex chars)
        /// 2. Address (0x + 40 hex chars)
        /// 3. Address with storage slot (0x + 40 hex chars + 0x + variable length)
        #[arg(short = 'i', long = "identifier")]
        identifier: String,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output", default_value = "./account_info")]
        output_path: String,
    },
    // /// Get statistics about the database
    // Stats {
    //     /// Path to the database file
    //     #[arg(short, long)]
    //     path: String,
    // },
}

fn parse_account_identifier(
    identifier: &str,
) -> Result<AccountIdentifier, Box<dyn std::error::Error>> {
    // Split by whitespace to handle address + slot format
    let parts: Vec<&str> = identifier.split_whitespace().collect();

    match parts.len() {
        1 => {
            let hex_str = parts[0].strip_prefix("0x").unwrap_or(parts[0]);
            match hex_str.len() {
                40 => Ok(AccountIdentifier::Address(parts[0].to_string())),
                64 | 128 => Ok(AccountIdentifier::FullHash(parts[0].to_string())),
                _ => Err(format!("Invalid identifier length. Must be either:\n- 40 hex chars for address\n- 64 or 128 hex chars for full hash\n- 40 hex chars + space + variable length for address with slot").into()),
            }
        },
        2 => {
            let address = parts[0];
            let slot = parts[1];
            // Validate address part
            let address_hex = address.strip_prefix("0x").unwrap_or(address);
            if address_hex.len() != 40 {
                return Err("Address part must be 40 hex characters (20 bytes)".into());
            }
            // Validate slot part has 0x prefix
            if !slot.starts_with("0x") {
                return Err("Storage slot must start with 0x".into());
            }
            Ok(AccountIdentifier::AddressWithSlot(address.to_string(), slot.to_string()))
        },
        _ => Err("Invalid identifier format. Expected either:\n- Single hex string\n- Address and storage slot separated by space".into()),
    }
}

fn identifier_to_nibbles(
    identifier: &AccountIdentifier,
) -> Result<Nibbles, Box<dyn std::error::Error>> {
    match identifier {
        AccountIdentifier::FullHash(hash) => {
            let hex_str = hash.strip_prefix("0x").unwrap_or(hash);
            let bytes = hex::decode(hex_str)?;
            Ok(Nibbles::unpack(&bytes))
        }
        AccountIdentifier::Address(address) => {
            let hex_str = address.strip_prefix("0x").unwrap_or(address);
            let bytes = hex::decode(hex_str)?;
            Ok(Nibbles::unpack(&bytes))
        }
        AccountIdentifier::AddressWithSlot(address, slot) => {
            let address_hex = address.strip_prefix("0x").unwrap_or(address);
            let slot_hex = slot.strip_prefix("0x").unwrap_or(slot);

            let address_bytes = hex::decode(address_hex)?;
            let slot_bytes = hex::decode(slot_hex)?;

            // Combine address and slot bytes
            let mut combined = address_bytes;
            combined.extend(slot_bytes);

            Ok(Nibbles::unpack(&combined))
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    match args.command {
        Commands::Print { db_path, page_id, output_path } => {
            print_page(&db_path, page_id, &output_path);
        }
        Commands::Account { db_path, identifier, output_path } => {
            get_account(&db_path, &identifier, &output_path);
        } /* Commands::Stats { path } => {
           *     get_stats(&path)?;
           * } */
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

fn get_account(db_path: &str, identifier: &str, output_path: &str) {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };
    //let mut context = db.start_read_only_transaction()?;

    // Parse the identifier into the appropriate format
    let account_id = parse_account_identifier(identifier)?;

    // Convert to nibbles
    let nibbles = identifier_to_nibbles(&account_id)?;

    // TODO: Use nibbles to look up account
    println!("Looking up account with identifier: {:?}", account_id);
    println!("Nibbles: {:?}", nibbles);

    db.get_account_or_storage(output_path, nibbles);

    Ok(())
}

// fn get_stats(db_path: &str) -> Result<(), Box<dyn std::error::Error>> {
//     let db = Database::open(db_path)?;
//     let mut context = db.start_read_only_transaction()?;
//     // TODO: Implement stats collection
//     println!("Getting database statistics");
//     Ok(())
// }
