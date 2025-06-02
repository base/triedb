use alloy_primitives::{hex, Address, StorageKey};
use alloy_trie::Nibbles;
use clap::{ArgAction, Parser, Subcommand, ValueEnum};
use std::{fs::File, io::Write, str};
use triedb::{
    page::PageId,
    path::{AddressPath, StoragePath},
    Database,
};

#[derive(Debug)]
enum TrieValueIdentifier {
    Address(String),                    // 40 chars
    StorageHash(String),                //128 chars
    AddressHash(String),                // 64 chars
    AddressWithStorage(String, String), // 40 chars + 64 chars
}

#[derive(Debug)]
enum TrieValuePath {
    Account(AddressPath),
    Storage(StoragePath),
}

#[derive(ValueEnum, Clone, Debug)]
enum VerbosityLevel {
    Normal,
    Verbose,
    ExtraVerbose,
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Print a specific page or all pages from the database
    Print {
        /// Path to the database file
        #[arg(short = 'd', long = "database")]
        db_path: String,

        /// Page ID to print (optional)
        #[arg(short = 'p', long = "page")]
        page_id: Option<PageId>,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output")]
        output_path: Option<String>,
    },

    /// Get information about a specific Trie Value
    TrieValue {
        /// Path to the database file
        #[arg(short = 'd', long = "database")]
        db_path: String,

        /// Account identifier in one of these formats:
        /// 1. Full hash (0x + 64 or 128 hex chars)
        /// 2. Address (0x + 40 hex chars)
        /// 3. Address with storage slot (0x + 40 hex chars + 0x + variable length)
        #[arg(short = 'i', long = "identifier", num_args = 1..)]
        identifier: Vec<String>,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output")]
        output_path: Option<String>,

        /// Verbosity level for output. Options are:
        /// [none] Print account information
        /// -v Print account/storage information and nodes accessed along the path
        /// -vv Print pages accessed along the path, along with the "-v"
        ///   information
        #[arg(short = 'v', long = "verbose", action = ArgAction::Count, default_value_t = 0)]
        verbosity: u8,
    },

    /// Print database information derived from RootPage
    RootPage {
        /// Path to the database file
        #[arg(short = 'd', long = "database")]
        db_path: String,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output")]
        output_path: Option<String>,
    },

    /// Print statistics about the database
    Statistics {
        /// Path to the database file
        #[arg(short = 'd', long = "database")]
        db_path: String,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output")]
        output_path: Option<String>,
    },

    /// Run consistency checks on the database
    ConsistencyCheck {
        /// Path to the database file
        #[arg(short = 'd', long = "database")]
        db_path: String,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output")]
        output_path: Option<String>,
    },
}

fn parse_trie_value_identifier(
    identifier: &str,
) -> Result<TrieValueIdentifier, Box<dyn std::error::Error>> {
    // Split by whitespace to handle address + slot format
    let parts: Vec<&str> = identifier.split_whitespace().collect();

    match parts.len() {
        1 => {
            let hex_str = parts[0].strip_prefix("0x").unwrap_or("");
            match hex_str.len() {
                40 => Ok(TrieValueIdentifier::Address(hex_str.to_string())),
                64 => Ok(TrieValueIdentifier::AddressHash(hex_str.to_string())),
                128 => Ok(TrieValueIdentifier::StorageHash(hex_str.to_string())),
                _ => Err("Invalid identifier format. Expected either: -Address: 0x<40 chars> -Address hash: 0x<64 chars> -Storage hash: 0x<128 chars> -Address and storage slot: 0x<40 chars> <storage slot>".into()),
            }
        },
        2 => {
            let address = parts[0];
            let slot = parts[1];
            // Validate address part
            let address_hex = address.strip_prefix("0x").unwrap_or("");
            if address_hex.len() != 40 {
                return Err("Address must be 0x +40 hex characters (20 bytes)".into());
            }
            // Validate slot part 
            let slot_hex = slot.strip_prefix("0x").unwrap_or("");
            if slot_hex.len() >= 64 || slot_hex.len() % 2 != 0 {
                return Err("Storage slot must be 0x +[2-64] hex characters (32 byte maximum), with an even number of characters".into());
            }
            Ok(TrieValueIdentifier::AddressWithStorage(address_hex.to_string(), slot_hex.to_string()))
        },
        _ => Err("Invalid identifier format. Expected either: -Address: 0x<40 chars> -Address hash: 0x<64 chars> -Storage hash: 0x<128 chars> -Address and storage slot: 0x<40 chars> <storage slot>".into()),
    }
}

fn identifier_to_trie_value_path(
    identifier: &TrieValueIdentifier,
) -> Result<TrieValuePath, Box<dyn std::error::Error>> {
    match identifier {
        TrieValueIdentifier::Address(address_str) => {
            let bytes: [u8; 20] = hex::decode(address_str)?.try_into().unwrap();
            Ok(TrieValuePath::Account(AddressPath::for_address(bytes.into())))
        }
        TrieValueIdentifier::AddressHash(acct_str) => {
            let bytes: [u8; 32] = hex::decode(acct_str)?.try_into().unwrap();
            Ok(TrieValuePath::Account(AddressPath::new(Nibbles::unpack(bytes))))
        }
        TrieValueIdentifier::StorageHash(strg_str) => {
            let bytes: [u8; 64] = hex::decode(strg_str)?.try_into().unwrap();
            let address_bytes: [u8; 32] = bytes[..32].try_into().unwrap();
            let address_path = AddressPath::new(Nibbles::unpack(address_bytes));

            let slot_bytes: [u8; 32] = bytes[32..64].try_into().unwrap();
            let slot_nibbles = Nibbles::unpack(slot_bytes);
            Ok(TrieValuePath::Storage(StoragePath::for_address_path_and_slot_hash(
                address_path,
                slot_nibbles,
            )))
        }
        TrieValueIdentifier::AddressWithStorage(address_str, storage_str) => {
            let address_bytes: [u8; 20] = hex::decode(address_str)?.try_into().unwrap();
            let address = Address::from_slice(&address_bytes);

            let storage_bytes = hex::decode(storage_str)?;
            let storage = StorageKey::left_padding_from(&storage_bytes);
            Ok(TrieValuePath::Storage(StoragePath::for_address_and_slot(address, storage)))
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    match args.command {
        Commands::Print { db_path, page_id, output_path } => {
            print_page(&db_path, page_id, output_path)?;
        }
        Commands::TrieValue { db_path, identifier, output_path, verbosity } => {
            let identifier_str = identifier.join(" ");
            get_trie_value(&db_path, &identifier_str, output_path, verbosity)?;
        }
        Commands::RootPage { db_path, output_path } => {
            root_page_info(&db_path, output_path)?;
        }
        Commands::Statistics { db_path, output_path } => {
            print_statistics(&db_path, output_path)?;
        }
        Commands::ConsistencyCheck { db_path, output_path } => {
            check_consistency(&db_path, output_path)?;
        }
    }

    Ok(())
}

fn print_page(
    db_path: &str,
    page_id: Option<PageId>,
    output_path: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };

    let output: Box<dyn Write> = if let Some(ref output_path) = output_path {
        Box::new(File::create(output_path)?)
    } else {
        Box::new(std::io::stdout())
    };

    match db.print_page(output, page_id) {
        Ok(_) => {
            if let Some(output_path) = output_path {
                println!("Page printed to {}", output_path);
            }
        }
        Err(e) => println!("Error printing page: {:?}", e),
    }
    Ok(())
}

fn get_trie_value(
    db_path: &str,
    identifier: &str,
    output_path: Option<String>,
    verbosity_level: u8,
) -> Result<(), Box<dyn std::error::Error>> {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };

    // Parse the identifier into the appropriate format
    let trie_value_id = parse_trie_value_identifier(identifier)?;

    // Convert to AddressPath or StoragePath
    let trie_value_path = identifier_to_trie_value_path(&trie_value_id)?;

    let output: Box<dyn Write> = if let Some(output_path) = output_path {
        Box::new(File::create(output_path)?)
    } else {
        Box::new(std::io::stdout())
    };

    let tx = db.begin_ro()?;
    match trie_value_path {
        TrieValuePath::Account(address_path) => {
            tx.debug_account(output, address_path, verbosity_level)?;
        }
        TrieValuePath::Storage(storage_path) => {
            tx.debug_storage(output, storage_path, verbosity_level)?;
        }
    }

    Ok(())
}

fn print_statistics(
    db_path: &str,
    output_path: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };

    let output: Box<dyn Write> = if let Some(ref output_path) = output_path {
        Box::new(File::create(output_path)?)
    } else {
        Box::new(std::io::stdout())
    };

    match db.print_statistics(output) {
        Ok(_) => {
            if let Some(output_path) = output_path {
                println!("Statistics printed to {}", output_path);
            }
        }
        Err(e) => println!("Error printing statistics: {:?}", e),
    }
    Ok(())
}

fn root_page_info(
    db_path: &str,
    output_path: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };

    let output: Box<dyn Write> = if let Some(ref output_path) = output_path {
        Box::new(File::create(output_path)?)
    } else {
        Box::new(std::io::stdout())
    };

    match db.root_page_info(output, db_path) {
        Ok(_) => {
            if let Some(output_path) = output_path {
                println!("Info written to {}", output_path);
            }
        }
        Err(e) => println!("Error printing root page info: {:?}", e),
    }
    Ok(())
}

fn check_consistency(
    db_path: &str,
    output_path: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };

    let output: Box<dyn Write> = if let Some(ref output_path) = output_path {
        Box::new(File::create(output_path)?)
    } else {
        Box::new(std::io::stdout())
    };

    match db.consistency_check(output, db_path) {
        Ok(_) => {
            if let Some(output_path) = output_path {
                println!("Consistency check results written to {}", output_path);
            }
        }
        Err(e) => println!("Error during consistency check: {:?}", e),
    }
    Ok(())
}
