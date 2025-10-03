use alloy_primitives::Address;
use rand::prelude::*;
use triedb::{path::AddressPath, Database};

pub const SEED_EOA: u64 = 42; // EOA seeding value
pub const BATCH_SIZE: usize = 10_000;

pub fn generate_random_address(rng: &mut StdRng) -> AddressPath {
    let addr = Address::random_with(rng);
    AddressPath::for_address(addr)
}

fn main() {
    let path = std::env::args().nth(1).unwrap();
    let db = Database::open(path).unwrap();
    let mut rng = StdRng::seed_from_u64(SEED_EOA);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();
    let mut tx = db.begin_ro().unwrap();
    addresses.iter().enumerate().for_each(|(i, addr)| {
        let a = tx.get_account(addr).unwrap();
        assert!(a.is_some(), "{:?}: account not found for address: {:?}", i, addr);
    });
    tx.commit().unwrap();
}
