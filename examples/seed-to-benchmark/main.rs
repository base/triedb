use alloy_primitives::{Address, StorageKey, StorageValue, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use rand::prelude::*;
use std::{env, str::FromStr};
use triedb::{
    account::Account,
    path::{AddressPath, StoragePath},
    transaction::TransactionError,
    Database,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum DatabaseType {
    Mmap,
    BufferPool,
}

impl FromStr for DatabaseType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "mmap" => Ok(DatabaseType::Mmap),
            "buffer-pool" => Ok(DatabaseType::BufferPool),
            _ => Err(()),
        }
    }
}

pub const DEFAULT_SETUP_DB_EOA_SIZE: usize = 1_000_000;
pub const DEFAULT_SETUP_DB_CONTRACT_SIZE: usize = 100_000;
pub const DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT: usize = 10;
const SEED_EOA: u64 = 42; // EOA seeding value
const SEED_CONTRACT: u64 = 43; // contract account seeding value

pub fn generate_random_address(rng: &mut StdRng) -> AddressPath {
    let addr = Address::random_with(rng);
    AddressPath::for_address(addr)
}

pub fn setup_database(
    db: &Database,
    repeat: usize,
    eoa_size: usize,
    contract_size: usize,
    storage_per_contract: usize,
) -> Result<(), TransactionError> {
    // Populate database with initial accounts
    let mut eoa_rng = StdRng::seed_from_u64(SEED_EOA);
    let mut contract_rng = StdRng::seed_from_u64(SEED_CONTRACT);
    for _i in 0..repeat {
        let mut tx = db.begin_rw()?;
        for i in 1..=eoa_size {
            let address = generate_random_address(&mut eoa_rng);
            let account =
                Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);

            tx.set_account(address, Some(account))?;
        }

        for i in 1..=contract_size {
            let address = generate_random_address(&mut contract_rng);
            let account =
                Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);

            tx.set_account(address.clone(), Some(account))?;

            // add random storage to each account
            for key in 1..=storage_per_contract {
                let storage_key = StorageKey::from(U256::from(key));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                let storage_value =
                    StorageValue::from_be_slice(storage_path.get_slot().pack().as_slice());

                tx.set_storage_slot(storage_path, Some(storage_value))?;
            }
        }

        tx.commit()?;
    }
    println!("root hash: {:?}", db.state_root());

    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let db_path = args.get(1).unwrap();
    let repeat = args.get(2).and_then(|s| s.parse::<usize>().ok()).unwrap_or(1);
    let eoa_size =
        args.get(3).and_then(|s| s.parse::<usize>().ok()).unwrap_or(DEFAULT_SETUP_DB_EOA_SIZE);
    let contract_size =
        args.get(4).and_then(|s| s.parse::<usize>().ok()).unwrap_or(DEFAULT_SETUP_DB_CONTRACT_SIZE);
    let storage_per_contract = args
        .get(5)
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT);
    let db_type =
        args.get(6).and_then(|s| s.parse::<DatabaseType>().ok()).unwrap_or(DatabaseType::Mmap);

    let db = match db_type {
        DatabaseType::Mmap => Database::create_new(db_path).unwrap(),
        DatabaseType::BufferPool => Database::create_new_with_buffer_pool(db_path).unwrap(),
    };
    println!("database type: {:?}", db_type);
    println!("eoa size: {}", eoa_size);
    println!("contract size: {}, storage per contract: {}", contract_size, storage_per_contract);
    println!("repeat {repeat} times");

    setup_database(&db, repeat, eoa_size, contract_size, storage_per_contract).unwrap();
}

// create 10 * (100_000 + 10*10_000) = 2M acc + storage (similar to 1m)
// ./target/release/examples/seed-to-benchmark ../seed/db 10 100000 10000 10 mmap
// ./target/release/examples/seed-to-benchmark ../seed/db.bp 1000 1000 100 10 buffer-pool
// ./target/release/examples/seed-to-benchmark ../seed/db.mm 1000 1000 100 10 mmap
