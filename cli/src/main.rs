use alloy_primitives::{hex, Address, StorageKey, U256};
use alloy_trie::Nibbles;
use clap::{Parser, Subcommand, ValueEnum};
use std::{fs::File, str};
use triedb::{
    path::{AddressPath, StoragePath},
    Database,
};

#[derive(Debug)]
enum TrieValueIdentifier {
    Address(String),                 // 40 chars
    StorageHash(String),             //128 chars
    AddressHash(String),             // 64 chars
    AddressWithStorage(String, u32), // 40 chars + 64 chars
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
        page_id: Option<u32>,

        /// Output filepath (optional)
        #[arg(short = 'o', long = "output", default_value = "./printed_page")]
        output_path: String,
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
        #[arg(short = 'o', long = "output", default_value = "./account_info")]
        output_path: String,

        /// Verbosity level for output. Options are:
        /// - Normal: Print account information
        /// - Verbose: Print account/storage information and node accessed along the path
        /// - ExtraVerbose: Print pages accessed along the path, along with the "verbose"
        ///   information
        #[arg(short = 'v', long = "verbose", value_enum, default_value_t = VerbosityLevel::Normal)]
        verbosity: VerbosityLevel,
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
            let slot_int = slot.parse::<u32>()?;
            Ok(TrieValueIdentifier::AddressWithStorage(address_hex.to_string(), slot_int))
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

            let storage = StorageKey::from(U256::from(*storage_str as usize));
            Ok(TrieValuePath::Storage(StoragePath::for_address_and_slot(address, storage)))
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    match args.command {
        Commands::Print { db_path, page_id, output_path } => {
            print_page(&db_path, page_id, &output_path);
        }
        Commands::TrieValue { db_path, identifier, output_path, verbosity } => {
            let identifier_str = identifier.join(" ");
            get_trie_value(&db_path, &identifier_str, &output_path, verbosity)?;
        }
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

fn get_trie_value(
    db_path: &str,
    identifier: &str,
    output_path: &str,
    verbosity: VerbosityLevel,
) -> Result<(), Box<dyn std::error::Error>> {
    let db = match Database::open(db_path) {
        Ok(db) => db,
        Err(e) => panic!("Could not open database: {:?}", e),
    };

    // Parse the identifier into the appropriate format
    let trie_value_id = parse_trie_value_identifier(identifier)?;

    // Convert to AddressPath or StoragePath
    let trie_value_path = identifier_to_trie_value_path(&trie_value_id)?;

    let output_file = File::create(output_path)?;

    // Convert verbosity level to string
    let verbosity_level = match verbosity {
        VerbosityLevel::Normal => 0,
        VerbosityLevel::Verbose => 1,
        VerbosityLevel::ExtraVerbose => 2,
    };

    let tx = db.begin_ro()?;
    match trie_value_path {
        TrieValuePath::Account(address_path) => {
            tx.debug_account(&output_file, address_path, verbosity_level)?;
        }
        TrieValuePath::Storage(storage_path) => {
            tx.debug_storage(&output_file, storage_path, verbosity_level)?;
        }
    }

    Ok(())
}
