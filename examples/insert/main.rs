use std::env;

use alloy_primitives::{Address, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use rand::prelude::*;
use triedb::{account::Account, path::AddressPath, Database};

fn generate_random_address(rng: &mut StdRng) -> AddressPath {
    let addr = Address::random_with(rng);
    AddressPath::for_address(addr)
}

fn main() {
    let dbfile = "test.db";
    let db = Database::create(dbfile).unwrap();
    let mut tx = db.begin_rw().unwrap();
    let mut rng = StdRng::seed_from_u64(42);
    let total_accounts = env::args().nth(1).and_then(|n| n.parse::<u64>().ok()).unwrap_or(3_000);

    println!(
        "[{}] begin insert",
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()
    );
    for i in 0..total_accounts {
        let address = generate_random_address(&mut rng);
        let account = Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        tx.set_account(address, Some(account)).unwrap();
    }
    tx.commit().unwrap();
    println!(
        "[{}] finished part 1",
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()
    );

    tx = db.begin_rw().unwrap();
    for i in 0..1 {
        let address = generate_random_address(&mut rng);
        let account = Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        tx.set_account(address, Some(account)).unwrap();
    }
    tx.commit().unwrap();
    println!(
        "[{}] end insert",
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()
    );
    // let root = db.state_root();
    // println!("root: {}", root);
}
