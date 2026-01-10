//! Tests for the storage engine.

use super::{helpers::find_shortest_common_prefix, *};
use crate::{
    account::Account,
    location::Location,
    node::{Node, TrieValue},
    page::{page_id, PageError, SlottedPage, SlottedPageMut},
    path::{AddressPath, RawPath, StoragePath},
    pointer::Pointer,
    storage::test_utils::{
        assert_metrics, create_test_account, create_test_engine, random_test_account,
    },
};
use alloy_primitives::{
    address, b256, hex, keccak256, Address, StorageKey, StorageValue, B256, U256,
};
use alloy_trie::{
    nodes::RlpNode,
    root::{storage_root_unhashed, storage_root_unsorted},
    Nibbles, EMPTY_ROOT_HASH, KECCAK_EMPTY,
};
use proptest::prelude::*;
use rand::{rngs::StdRng, seq::SliceRandom, Rng, RngCore, SeedableRng};
use std::collections::{HashMap, HashSet};

#[test]
fn test_allocate_get_mut_clone() {
    let (storage_engine, mut context) = create_test_engine(300);

    // Initial allocation
    let mut page = storage_engine.allocate_page(&mut context).unwrap();
    assert_eq!(page.id(), page_id!(1));
    assert_eq!(page.contents()[0], 0);
    assert_eq!(page.snapshot_id(), 1);
    assert_metrics(&context, 0, 1, 0, 0);

    // mutation
    page.contents_mut()[0] = 123;
    drop(page);
    storage_engine.commit(&context).unwrap();

    context = storage_engine.write_context();

    // reading mutated page
    let page = storage_engine.get_page(&context, page_id!(1)).unwrap();
    assert_eq!(page.id(), page_id!(1));
    assert_eq!(page.contents()[0], 123);
    assert_eq!(page.snapshot_id(), 1);
    assert_metrics(&context, 1, 0, 0, 0);

    // cloning a page should allocate a new page and orphan the original page
    let cloned_page = storage_engine.get_mut_clone(&mut context, page_id!(1)).unwrap();
    assert_eq!(cloned_page.id(), page_id!(2));
    assert_eq!(cloned_page.contents()[0], 123);
    assert_eq!(cloned_page.snapshot_id(), 2);
    assert_ne!(cloned_page.id(), page.id());
    assert_metrics(&context, 2, 1, 0, 0);

    // the next allocation should not come from the orphaned page, as the snapshot id is the
    // same as when the page was orphaned
    let page = storage_engine.allocate_page(&mut context).unwrap();
    assert_eq!(page.id(), 3);
    assert_eq!(page.contents()[0], 0);
    assert_eq!(page.snapshot_id(), 2);
    assert_metrics(&context, 2, 2, 0, 0);
    drop(page);

    storage_engine.commit(&context).unwrap();

    context = storage_engine.write_context();

    // the next allocation should not come from the orphaned page, as the snapshot has not been
    // unlocked yet
    let page = storage_engine.allocate_page(&mut context).unwrap();
    assert_eq!(page.id(), 4);
    assert_eq!(page.contents()[0], 0);
    assert_eq!(page.snapshot_id(), 3);
    assert_metrics(&context, 0, 1, 0, 0);
    drop(page);

    storage_engine.unlock(3);

    // the next allocation should come from the orphaned page because the snapshot id has
    // increased. The page data should be zeroed out.
    let page = storage_engine.allocate_page(&mut context).unwrap();
    assert_eq!(page.id(), 1);
    assert_eq!(page.contents()[0], 0);
    assert_eq!(page.snapshot_id(), 3);
    assert_metrics(&context, 1, 1, 1, 0);
    drop(page);

    // assert that the metadata tracks the largest page number
    assert_eq!(context.page_count, 4);
}

#[test]
fn test_shared_page_mutability() {
    let (storage_engine, mut context) = create_test_engine(300);

    let page = storage_engine.allocate_page(&mut context).unwrap();
    assert_eq!(page.id(), page_id!(1));
    assert_eq!(page.contents()[0], 0);
    assert_metrics(&context, 0, 1, 0, 0);
    drop(page);

    let mut page_mut = storage_engine.get_mut_page(&context, page_id!(1)).unwrap();
    page_mut.contents_mut()[0] = 123;
    assert_metrics(&context, 1, 1, 0, 0);
    drop(page_mut);

    storage_engine.commit(&context).unwrap();

    let page = storage_engine.get_page(&context, page_id!(1)).unwrap();
    assert_eq!(page.contents()[0], 123);
    assert_metrics(&context, 2, 1, 0, 0);
}

#[test]
fn test_set_get_account() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));
    assert_metrics(&context, 0, 1, 0, 0);

    let test_cases = vec![
        (address!("0x4200000000000000000000000000000000000015"), create_test_account(123, 456)),
        (address!("0x4200000000000000000000000000000000000016"), create_test_account(999, 999)),
        (address!("0x4200000000000000000000000000000000000002"), create_test_account(1000, 1000)),
        (address!("0x4200000000000000000000000000000000000000"), create_test_account(1001, 1001)),
    ];

    // Insert accounts and verify they don't exist before insertion
    for (address, account) in &test_cases {
        let path = AddressPath::for_address(*address);

        let read_account = storage_engine.get_account(&mut context, &path).unwrap();
        assert_eq!(read_account, None);

        storage_engine
            .set_values(&mut context, vec![(path.into(), Some(account.clone().into()))].as_mut())
            .unwrap();
    }

    // Verify all accounts exist after insertion
    for (address, account) in test_cases {
        let read_account =
            storage_engine.get_account(&mut context, &AddressPath::for_address(address)).unwrap();
        assert_eq!(read_account, Some(account));
    }
}

#[test]
fn test_simple_trie_state_root_1() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address1 = address!("0x8e64566b5eb8f595f7eb2b8d302f2e5613cb8bae");
    let account1 = create_test_account(1_000_000_000_000_000_000u64, 0);
    let path1 = AddressPath::for_address(address1);

    let address2 = address!("0xcea8f2236efa20c8fadeb9d66e398a6532cca6c8");
    let account2 = create_test_account(14_000_000_000_000_000_000u64, 1);
    let path2 = AddressPath::for_address(address2);

    storage_engine
        .set_values(
            &mut context,
            vec![
                (path1.into(), Some(account1.clone().into())),
                (path2.into(), Some(account2.clone().into())),
            ]
            .as_mut(),
        )
        .unwrap();
    assert_metrics(&context, 1, 1, 0, 0);

    assert_eq!(
        context.root_node_hash,
        b256!("0x0d9348243d7357c491e6a61f4b1305e77dc6acacdb8cc708e662f6a9bab6ca02")
    );
}

#[test]
fn test_simple_trie_state_root_2() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address1 = address!("0x000f3df6d732807ef1319fb7b8bb8522d0beac02");
    let account1 = Account::new(1, U256::from(0), EMPTY_ROOT_HASH, keccak256(hex!("0x3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f35801560495762001fff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b62001fff42064281555f359062001fff015500")));
    let path1 = AddressPath::for_address(address1);

    let address2 = address!("0x0000000000000000000000000000000000001000");
    let account2 = Account::new(1, U256::from(0x010000000000u64), EMPTY_ROOT_HASH, keccak256(hex!("0x366000602037602060003660206000720f3df6d732807ef1319fb7b8bb8522d0beac02620186a0f16000556000516001553d6002553d600060003e600051600355")));
    let path2 = AddressPath::for_address(address2);

    let address3 = address!("0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b");
    let account3 =
        Account::new(0, U256::from(0x3635c9adc5dea00000u128), EMPTY_ROOT_HASH, KECCAK_EMPTY);
    let path3 = AddressPath::for_address(address3);

    storage_engine
        .set_values(
            &mut context,
            vec![
                (path1.into(), Some(account1.into())),
                (path2.into(), Some(account2.into())),
                (path3.into(), Some(account3.into())),
            ]
            .as_mut(),
        )
        .unwrap();
    assert_metrics(&context, 1, 1, 0, 0);

    assert_eq!(
        context.root_node_hash,
        b256!("0x6f78ee01791dd8a62b4e2e86fae3d7957df9fa7f7a717ae537f90bb0c79df296")
    );

    let account1_storage = [
        (B256::with_last_byte(0x0c), U256::from(0x0c)),
        (
            b256!("0x000000000000000000000000000000000000000000000000000000000000200b"),
            b256!("0x6c31fc15422ebad28aaf9089c306702f67540b53c7eea8b7d2941044b027100f").into(),
        ),
    ];

    let account2_storage = vec![
        (B256::with_last_byte(0x00), U256::from(0x01)),
        (
            B256::with_last_byte(0x01),
            b256!("0x6c31fc15422ebad28aaf9089c306702f67540b53c7eea8b7d2941044b027100f").into(),
        ),
        (B256::with_last_byte(0x02), U256::from(0x20)),
        (
            B256::with_last_byte(0x03),
            b256!("0x6c31fc15422ebad28aaf9089c306702f67540b53c7eea8b7d2941044b027100f").into(),
        ),
    ];

    let account3_updated =
        Account::new(1, U256::from(0x3635c9adc5de938d5cu128), EMPTY_ROOT_HASH, KECCAK_EMPTY);

    let mut changes = Vec::<(RawPath, Option<TrieValue>)>::new();

    changes.extend(account1_storage.map(|(key, value)| {
        (StoragePath::for_address_and_slot(address1, key).into(), Some(TrieValue::Storage(value)))
    }));

    changes.extend(account2_storage.into_iter().map(|(key, value)| {
        (StoragePath::for_address_and_slot(address2, key).into(), Some(TrieValue::Storage(value)))
    }));

    changes.push((
        AddressPath::for_address(address3).into(),
        Some(TrieValue::Account(account3_updated)),
    ));

    storage_engine.set_values(&mut context, changes.as_mut()).unwrap();
    assert_metrics(&context, 2, 1, 0, 0);

    assert_eq!(
        context.root_node_hash,
        b256!("0xf869dcb9ef8893f6b30bf495847fd99166aaf790ed962c468d11a826996ab2d2")
    );
}

#[test]
fn test_trie_state_root_order_independence() {
    let mut rng = StdRng::seed_from_u64(1);

    // create 100 accounts with random addresses, balances, and storage values
    let mut accounts = Vec::new();
    for idx in 0..100 {
        let address = Address::random_with(&mut rng);
        let account = random_test_account(&mut rng);
        let mut storage = Vec::new();
        if idx % 10 == 0 {
            for _ in 0..rng.random_range(1..25) {
                let slot = StorageKey::random_with(&mut rng);
                storage.push((slot, StorageValue::from(rng.next_u64())));
            }
        }
        accounts.push((address, account, storage));
    }

    let (storage_engine, mut context) = create_test_engine(30000);

    // insert accounts and storage in random order
    accounts.shuffle(&mut rng);
    let mut changes = vec![];
    for (address, account, mut storage) in accounts.clone() {
        changes.push((AddressPath::for_address(address).into(), Some(TrieValue::Account(account))));
        storage.shuffle(&mut rng);
        for (slot, value) in storage {
            changes.push((
                StoragePath::for_address_and_slot(address, slot).into(),
                Some(TrieValue::Storage(value)),
            ));
        }
    }
    storage_engine.set_values(&mut context, &mut changes).unwrap();

    // commit the changes
    storage_engine.commit(&context).unwrap();

    let state_root = context.root_node_hash;

    let mut expected_account_storage_roots = HashMap::new();

    // check that all of the values are correct
    for (address, account, storage) in accounts.clone() {
        let read_account = storage_engine
            .get_account(&mut context, &AddressPath::for_address(address))
            .unwrap()
            .unwrap();
        assert_eq!(read_account.balance, account.balance);

        for (slot, value) in storage {
            let read_value = storage_engine
                .get_storage(&mut context, &StoragePath::for_address_and_slot(address, slot))
                .unwrap();
            assert_eq!(read_value, Some(value));
        }

        expected_account_storage_roots.insert(address, read_account.storage_root);
    }

    let (storage_engine, mut context) = create_test_engine(30000);

    // insert accounts in a different random order, but only after inserting different values
    // first
    accounts.shuffle(&mut rng);
    for (address, _, mut storage) in accounts.clone() {
        storage_engine
            .set_values(
                &mut context,
                vec![(
                    AddressPath::for_address(address).into(),
                    Some(random_test_account(&mut rng).into()),
                )]
                .as_mut(),
            )
            .unwrap();

        storage.shuffle(&mut rng);
        for (slot, _) in storage {
            storage_engine
                .set_values(
                    &mut context,
                    vec![(
                        StoragePath::for_address_and_slot(address, slot).into(),
                        Some(StorageValue::from(rng.next_u64()).into()),
                    )]
                    .as_mut(),
                )
                .unwrap();
        }
    }

    accounts.shuffle(&mut rng);
    for (address, account, mut storage) in accounts.clone() {
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(address).into(), Some(account.into()))].as_mut(),
            )
            .unwrap();

        storage.shuffle(&mut rng);
        for (slot, value) in storage {
            storage_engine
                .set_values(
                    &mut context,
                    vec![(
                        StoragePath::for_address_and_slot(address, slot).into(),
                        Some(value.into()),
                    )]
                    .as_mut(),
                )
                .unwrap();
        }
    }

    // commit the changes
    storage_engine.commit(&context).unwrap();

    // check that all of the values are correct
    for (address, account, storage) in accounts.clone() {
        let read_account = storage_engine
            .get_account(&mut context, &AddressPath::for_address(address))
            .unwrap()
            .unwrap();
        assert_eq!(read_account.balance, account.balance);
        assert_eq!(read_account.nonce, account.nonce);
        assert_eq!(read_account.storage_root, expected_account_storage_roots[&address]);
        for (slot, value) in storage {
            let read_value = storage_engine
                .get_storage(&mut context, &StoragePath::for_address_and_slot(address, slot))
                .unwrap();
            assert_eq!(read_value, Some(value));
        }
    }

    // verify the state root is the same
    assert_eq!(state_root, context.root_node_hash);
}

#[test]
fn test_set_get_account_common_prefix() {
    let (storage_engine, mut context) = create_test_engine(300);

    let test_accounts = vec![
        (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"), create_test_account(100, 1)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"), create_test_account(123, 456)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"), create_test_account(999, 999)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000004"), create_test_account(1000, 1000)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000030000000000000000000000000000000005"), create_test_account(1001, 1001)),
    ];

    // Insert all accounts
    for (nibbles, account) in test_accounts.iter() {
        let path = AddressPath::new(Nibbles::from_nibbles(*nibbles));
        storage_engine
            .set_values(&mut context, vec![(path.into(), Some(account.clone().into()))].as_mut())
            .unwrap();
    }

    // Verify all accounts exist
    for (nibbles, account) in test_accounts {
        let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
        let read_account = storage_engine.get_account(&mut context, &path).unwrap();
        assert_eq!(read_account, Some(account));
    }
}

#[test]
fn test_split_page() {
    let (storage_engine, mut context) = create_test_engine(300);

    let test_accounts = vec![
        (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"), create_test_account(100, 1)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002"), create_test_account(123, 456)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"), create_test_account(999, 999)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000004"), create_test_account(1000, 1000)),
        (hex!("00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000030000000000000000000000000000000005"), create_test_account(1001, 1001)),
    ];

    // Insert accounts
    for (nibbles, account) in test_accounts.iter() {
        let path = AddressPath::new(Nibbles::from_nibbles(*nibbles));
        storage_engine
            .set_values(&mut context, vec![(path.into(), Some(account.clone().into()))].as_mut())
            .unwrap();
    }

    // Split the page
    let page = storage_engine.get_mut_page(&context, page_id!(1)).unwrap();
    let mut slotted_page = SlottedPageMut::try_from(page).unwrap();
    storage_engine.split_page(&mut context, &mut slotted_page).unwrap();
    drop(slotted_page);

    // Verify all accounts still exist after split
    for (nibbles, account) in test_accounts {
        let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
        let read_account = storage_engine.get_account(&mut context, &path).unwrap();
        assert_eq!(read_account, Some(account));
    }
}

#[test]
fn test_insert_get_1000_accounts() {
    let (storage_engine, mut context) = create_test_engine(5000);

    for i in 0..1000 {
        let path = address_path_for_idx(i);
        let account = create_test_account(i, i);
        storage_engine
            .set_values(
                &mut context,
                vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();
    }

    for i in 0..1000 {
        let path = address_path_for_idx(i);
        let account = storage_engine.get_account(&mut context, &path).unwrap();
        assert_eq!(account, Some(create_test_account(i, i)));
    }
}

#[test]
#[should_panic]
fn test_set_storage_slot_with_no_account_panics() {
    let (storage_engine, mut context) = create_test_engine(300);
    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");

    let storage_key = b256!("0x0000000000000000000000000000000000000000000000000000000000000000");
    let storage_value = b256!("0x0000000000000000000000000000000000000000000000000000000062617365");

    let storage_path = StoragePath::for_address_and_slot(address, storage_key);

    let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

    storage_engine
        .set_values(&mut context, vec![(storage_path.into(), Some(storage_value.into()))].as_mut())
        .unwrap();
}

#[test]
fn test_get_account_storage_cache() {
    let (storage_engine, mut context) = create_test_engine(300);
    {
        // An account with no storage should not be cached
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96555");
        let address_path = AddressPath::for_address(address);
        let account = create_test_account(22, 22);

        storage_engine
            .set_values(
                &mut context,
                vec![((&address_path).into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        let read_account =
            storage_engine.get_account(&mut context, &address_path).unwrap().unwrap();
        assert_eq!(read_account, account);
        let cached_location = context.contract_account_loc_cache.get(&(&address_path).into());
        assert!(cached_location.is_none());
    }
    {
        // An account with storage should be cache when read the account first
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let address_path = AddressPath::for_address(address);
        let account = create_test_account(100, 1);

        storage_engine
            .set_values(
                &mut context,
                vec![(address_path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        let test_cases = [
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
            ),
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
            ),
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
            ),
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
            ),
        ];
        storage_engine
            .set_values(
                &mut context,
                test_cases
                    .iter()
                    .map(|(key, value)| {
                        let storage_path = StoragePath::for_address_and_slot(address, *key);
                        let storage_value = StorageValue::from_be_slice(value.as_slice());
                        (storage_path.into(), Some(storage_value.into()))
                    })
                    .collect::<Vec<(RawPath, Option<TrieValue>)>>()
                    .as_mut(),
            )
            .unwrap();

        let read_account = storage_engine
            .get_account(&mut context, &AddressPath::for_address(address))
            .unwrap()
            .unwrap();
        assert_eq!(read_account.balance, account.balance);
        assert_eq!(read_account.nonce, account.nonce);
        assert_ne!(read_account.storage_root, EMPTY_ROOT_HASH);

        // the account should be cached
        let account_cache_location =
            context.contract_account_loc_cache.get(&(&address_path).into()).unwrap();
        assert_eq!(account_cache_location.0, 1);
        assert_eq!(account_cache_location.1, 2); // 0 is the branch page, 1 is the first EOA
                                                 // account, 2 is the this contract account

        // getting the storage slot should hit the cache
        let storage_path = StoragePath::for_address_and_slot(address, test_cases[0].0);
        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(
            read_storage_slot,
            Some(StorageValue::from_be_slice(
                b256!("0x0000000000000000000000000000000000000000000000000000000062617365")
                    .as_slice()
            ))
        );
        assert_eq!(context.transaction_metrics.get_cache_storage_read(), (1, 0));
    }
    {
        // Write into the storage slot should invalidate the cache
        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96066");
        let address_path = AddressPath::for_address(address);
        let account = create_test_account(234, 567);

        storage_engine
            .set_values(
                &mut context,
                vec![(address_path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        let test_cases = [
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
                b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
            ),
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
                b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
            ),
        ];
        storage_engine
            .set_values(
                &mut context,
                test_cases
                    .iter()
                    .map(|(key, value)| {
                        let storage_path = StoragePath::for_address_and_slot(address, *key);
                        let storage_value = StorageValue::from_be_slice(value.as_slice());
                        (storage_path.into(), Some(storage_value.into()))
                    })
                    .collect::<Vec<(RawPath, Option<TrieValue>)>>()
                    .as_mut(),
            )
            .unwrap();

        storage_engine
            .get_account(&mut context, &AddressPath::for_address(address))
            .unwrap()
            .unwrap();

        let test_cases = [
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
                b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
            ),
            (
                b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
                b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
            ),
        ];
        storage_engine
            .set_values(
                &mut context,
                test_cases
                    .iter()
                    .map(|(key, value)| {
                        let storage_path = StoragePath::for_address_and_slot(address, *key);
                        let storage_value = StorageValue::from_be_slice(value.as_slice());
                        (storage_path.into(), Some(storage_value.into()))
                    })
                    .collect::<Vec<(RawPath, Option<TrieValue>)>>()
                    .as_mut(),
            )
            .unwrap();

        // the cache should be invalidated
        let account_cache_location =
            context.contract_account_loc_cache.get(&(&address_path).into());
        assert!(account_cache_location.is_none());
    }
}

#[test]
fn test_set_get_account_storage_slots() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let test_cases = vec![
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
            b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
            b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
            b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
            b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
        ),
    ];

    // Insert storage slots and verify they don't exist before insertion
    for (storage_key, _) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);
        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(read_storage_slot, None);
    }
    storage_engine
        .set_values(
            &mut context,
            test_cases
                .iter()
                .map(|(key, value)| {
                    let storage_path = StoragePath::for_address_and_slot(address, *key);
                    let storage_value = StorageValue::from_be_slice(value.as_slice());
                    (storage_path.into(), Some(storage_value.into()))
                })
                .collect::<Vec<(RawPath, Option<TrieValue>)>>()
                .as_mut(),
        )
        .unwrap();

    // Verify all storage slots exist after insertion
    for (storage_key, storage_value) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);
        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());
        assert_eq!(read_storage_slot, Some(storage_value));
    }
}

#[test]
fn test_set_get_account_storage_roots() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let test_cases = vec![
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
            b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
            b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
            b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
            b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
        ),
    ];

    // Insert storage slots and verify they don't exist before insertion
    for (storage_key, storage_value) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(read_storage_slot, None);

        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

        storage_engine
            .set_values(
                &mut context,
                vec![(storage_path.into(), Some(storage_value.into()))].as_mut(),
            )
            .unwrap();
    }

    // Verify the storage roots is correct. The storage root should be equivalent to the hash
    // of a trie that was initially empty and then filled with these key/values.
    let expected_root = storage_root_unhashed(test_cases.into_iter().map(|(key, value)| {
        (key, U256::from_be_bytes::<32>(value.as_slice().try_into().unwrap()))
    }));

    let account = storage_engine
        .get_account(&mut context, &AddressPath::for_address(address))
        .unwrap()
        .unwrap();

    assert_eq!(account.storage_root, expected_root);
}

#[test]
fn test_set_get_many_accounts_storage_roots() {
    let (storage_engine, mut context) = create_test_engine(2000);

    for i in 0..100 {
        let address = Address::from_slice(&keccak256((i as u32).to_le_bytes()).as_slice()[0..20]);
        let path = AddressPath::for_address(address);
        let account = create_test_account(i, i);
        storage_engine
            .set_values(&mut context, vec![(path.into(), Some(account.clone().into()))].as_mut())
            .unwrap();
    }

    for i in 0..100 {
        let address = Address::from_slice(&keccak256((i as u32).to_le_bytes()).as_slice()[0..20]);
        let path = AddressPath::for_address(address);
        let mut keys_values = Vec::new();
        for j in 0..25 {
            let storage_slot_key: StorageKey = B256::repeat_byte(j as u8);
            let storage_slot_value: StorageValue = B256::with_last_byte(j as u8).into();

            let storage_path = StoragePath::for_address_and_slot(address, storage_slot_key);
            storage_engine
                .set_values(
                    &mut context,
                    vec![(storage_path.clone().into(), Some(storage_slot_value.into()))].as_mut(),
                )
                .unwrap();

            keys_values.push((
                B256::from_slice(storage_path.get_slot().pack().as_slice()),
                storage_slot_value,
            ))
        }

        let expected_root = storage_root_unsorted(keys_values.into_iter());

        // check the storage root of the account
        let account = storage_engine.get_account(&mut context, &path).unwrap().unwrap();

        assert_eq!(account.storage_root, expected_root);
    }
}

#[test]
fn test_split_page_stress() {
    // Create a storage engine with limited pages to force splits
    let (storage_engine, mut context) = create_test_engine(5000);

    // Create a large number of accounts with different patterns to stress the trie

    // Pattern 1: Accounts with common prefixes to create deep branches
    let mut accounts = Vec::new();
    for i in 0..4096 {
        // Create paths with common prefixes but different endings
        let mut nibbles = [0u8; 64];
        // First 32 nibbles are the same
        for (j, nibble) in nibbles[0..32].iter_mut().enumerate() {
            *nibble = (j % 16) as u8;
        }
        // Last 30 nibbles vary
        for (j, nibble) in nibbles[32..64].iter_mut().enumerate() {
            *nibble = ((i + j) % 16) as u8;
        }

        nibbles[61] = (i % 16) as u8;
        nibbles[62] = ((i / 16) % 16) as u8;
        nibbles[63] = ((i / 256) % 16) as u8;

        let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
        let account = create_test_account(i as u64 * 1000, i as u64);
        accounts.push((path, account));
    }

    // Pattern 2: Accounts with very different paths to create wide branches
    for i in 0..4096 {
        let mut nibbles = [0u8; 64];
        // Make each path start with a different nibble
        nibbles[0] = (i % 16) as u8;
        nibbles[1] = ((i / 16) % 16) as u8;
        nibbles[2] = ((i / 256) % 16) as u8;
        // Fill the rest with a pattern
        for (j, nibble) in nibbles[3..64].iter_mut().enumerate() {
            *nibble = ((i * j) % 16) as u8;
        }

        let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
        let account = create_test_account(i as u64 * 2000, i as u64 * 2);
        accounts.push((path, account));
    }

    // Pattern 3: Accounts with paths that will cause specific branch splits
    for i in 0..4096 {
        let mut nibbles = [0u8; 64];
        // First half of paths share prefix, second half different
        if i < 50 {
            nibbles[0] = 10; // Arbitrary value
            for (j, nibble) in nibbles[1..62].iter_mut().enumerate() {
                *nibble = ((i + j) % 16) as u8;
            }
        } else {
            nibbles[0] = 11; // Different arbitrary value
            for (j, nibble) in nibbles[1..62].iter_mut().enumerate() {
                *nibble = ((i + j) % 16) as u8;
            }
        }

        nibbles[61] = (i % 16) as u8;
        nibbles[62] = ((i / 16) % 16) as u8;
        nibbles[63] = ((i / 256) % 16) as u8;

        let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
        let account = create_test_account(i as u64 * 3000, i as u64 * 3);
        accounts.push((path, account));
    }

    // Ensure there are no duplicate paths
    let mut unique_paths = std::collections::HashSet::new();
    for (path, _) in &accounts {
        assert!(unique_paths.insert(path.clone()), "Duplicate path found: {path:?}");
    }

    // Insert all accounts
    for (path, account) in &accounts {
        storage_engine
            .set_values(
                &mut context,
                vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();
    }

    // Verify all accounts exist with correct values
    for (path, expected_account) in &accounts {
        let retrieved_account = storage_engine.get_account(&mut context, path).unwrap();
        assert_eq!(
            retrieved_account,
            Some(expected_account.clone()),
            "Account mismatch for path: {path:?}"
        );
    }

    // Force multiple splits to stress the system
    // Find all pages in the trie and split them recursively
    let mut pages_to_split = vec![context.root_node_page_id.unwrap()];
    while let Some(page_id) = pages_to_split.pop() {
        let page_result = storage_engine.get_mut_page(&context, page_id);
        if matches!(page_result, Err(Error::PageError(PageError::PageNotFound(_)))) {
            break;
        }
        let mut slotted_page = SlottedPageMut::try_from(page_result.unwrap()).unwrap();

        // Try to split this page
        if storage_engine.split_page(&mut context, &mut slotted_page).is_ok() {
            // If split succeeded, add the new pages to be processed
            pages_to_split.push(page_id.inc().unwrap()); // New page created by split
        }
    }

    // Verify all accounts still exist with correct values after splits
    for (path, expected_account) in &accounts {
        let retrieved_account = storage_engine.get_account(&mut context, path).unwrap();
        assert_eq!(
            retrieved_account,
            Some(expected_account.clone()),
            "Account mismatch after split for path: {path:?}"
        );
    }

    // Add more accounts after splitting to ensure the structure is still valid
    let mut additional_accounts = Vec::new();
    for i in 0..50 {
        let mut nibbles = [0u8; 64];
        // Create some completely new paths
        nibbles[0] = 15; // Different from previous patterns
        for (j, nibble) in nibbles[1..62].iter_mut().enumerate() {
            *nibble = ((i * j + 7) % 16) as u8; // Different pattern
        }

        nibbles[62] = (i % 16) as u8;
        nibbles[63] = ((i / 16) % 16) as u8;

        let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
        let account = create_test_account(i as u64 * 5000, i as u64 * 5);
        additional_accounts.push((path, account));
    }

    // Insert additional accounts
    storage_engine
        .set_values(
            &mut context,
            additional_accounts
                .iter()
                .map(|(path, account)| (path.clone().into(), Some(account.clone().into())))
                .collect::<Vec<(RawPath, Option<TrieValue>)>>()
                .as_mut(),
        )
        .unwrap();

    // Verify all original accounts still exist
    for (path, expected_account) in &accounts {
        let retrieved_account = storage_engine.get_account(&mut context, path).unwrap();
        assert_eq!(
            retrieved_account,
            Some(expected_account.clone()),
            "Original account lost after adding new accounts"
        );
    }

    // Verify all new accounts exist
    for (path, expected_account) in &additional_accounts {
        let retrieved_account = storage_engine.get_account(&mut context, path).unwrap();
        assert_eq!(retrieved_account, Some(expected_account.clone()), "New account not found");
    }
    // Verify the pages split metric
    assert!(context.transaction_metrics.get_pages_split() > 0);
}

#[test]
fn test_split_page_random_accounts() {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    // Create a storage engine
    let (storage_engine, mut context) = create_test_engine(2000);

    // Use a seeded RNG for reproducibility
    let mut rng = StdRng::seed_from_u64(42);

    // Generate a large number of random accounts
    let mut accounts = Vec::new();
    for _ in 0..3000 {
        let mut nibbles = [0u8; 64];
        // Generate random nibbles
        for nibble in &mut nibbles {
            *nibble = rng.random_range(0..16) as u8;
        }

        let path = AddressPath::new(Nibbles::from_nibbles(nibbles));
        let balance = rng.random_range(0..1_000_000);
        let nonce = rng.random_range(0..100);
        let account = create_test_account(balance, nonce);
        accounts.push((path, account));
    }

    // Insert all accounts
    storage_engine
        .set_values(
            &mut context,
            accounts
                .clone()
                .into_iter()
                .map(|(path, account)| (path.into(), Some(account.into())))
                .collect::<Vec<(RawPath, Option<TrieValue>)>>()
                .as_mut(),
        )
        .unwrap();

    // Verify all accounts exist with correct values
    for (path, expected_account) in &accounts {
        let retrieved_account = storage_engine.get_account(&mut context, path).unwrap();
        assert_eq!(retrieved_account, Some(expected_account.clone()));
    }

    // Get all pages and force splits on them
    let mut page_ids = Vec::new();
    // Start with the root page
    page_ids.push(context.root_node_page_id.unwrap());

    // Process each page
    for i in 0..page_ids.len() {
        let page_id = page_ids[i];

        // Try to get and split the page
        if let Ok(page) = storage_engine.get_mut_page(&context, page_id) {
            if let Ok(mut slotted_page) = SlottedPageMut::try_from(page) {
                // Force a split
                let _ = storage_engine.split_page(&mut context, &mut slotted_page);

                // Get the node to find child pages
                if let Ok(node) = slotted_page.get_value::<Node>(0) {
                    // Add child pages to our list
                    for (_, child_ptr) in node.enumerate_children().expect("can get children") {
                        if let Some(child_page_id) = child_ptr.location().page_id() {
                            if !page_ids.contains(&child_page_id) {
                                page_ids.push(child_page_id);
                            }
                        }
                    }
                }
            }
        }
    }

    // Verify all accounts still exist with correct values after splits
    for (path, expected_account) in &accounts {
        let retrieved_account = storage_engine.get_account(&mut context, path).unwrap();
        assert_eq!(
            retrieved_account,
            Some(expected_account.clone()),
            "Account mismatch after splitting multiple pages"
        );
    }

    // Create a vector to store updates
    let mut updates = Vec::new();

    // Prepare updates for some existing accounts
    for (i, (path, _)) in accounts.iter().enumerate() {
        if i.is_multiple_of(5) {
            // Update every 5th account
            let new_balance = rng.random_range(0..1_000_000);
            let new_nonce = rng.random_range(0..100);
            let new_account = create_test_account(new_balance, new_nonce);

            updates.push((i, path.clone(), new_account));
        }
    }

    // Apply the updates to both the trie and our test data
    for (idx, path, new_account) in &updates {
        // Update in the trie
        storage_engine
            .set_values(
                &mut context,
                vec![(path.clone().into(), Some(new_account.clone().into()))].as_mut(),
            )
            .unwrap();

        // Update in our test data
        accounts[*idx] = (path.clone(), new_account.clone());
    }

    // Verify all accounts have correct values after updates
    for (path, expected_account) in &accounts {
        let retrieved_account = storage_engine.get_account(&mut context, path).unwrap();
        assert_eq!(
            retrieved_account,
            Some(expected_account.clone()),
            "Account mismatch after updates"
        );
    }
}

#[test]
fn test_delete_account() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_metrics(&context, 0, 1, 0, 0);

    // Check that the account exists
    let read_account =
        storage_engine.get_account(&mut context, &AddressPath::for_address(address)).unwrap();
    assert_eq!(read_account, Some(account.clone()));

    // Reset the context metrics
    context.transaction_metrics = Default::default();
    storage_engine
        .set_values(&mut context, vec![(AddressPath::for_address(address).into(), None)].as_mut())
        .unwrap();
    assert_metrics(&context, 1, 0, 0, 0);

    // Verify the account is deleted
    let read_account =
        storage_engine.get_account(&mut context, &AddressPath::for_address(address)).unwrap();
    assert_eq!(read_account, None);
}

#[test]
fn test_delete_accounts() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let test_cases = vec![
        (address!("0x4200000000000000000000000000000000000015"), create_test_account(123, 456)),
        (address!("0x4200000000000000000000000000000000000016"), create_test_account(999, 999)),
        (address!("0x4200000000000000000000000000000000000002"), create_test_account(1000, 1000)),
        (address!("0x4200000000000000000000000000000000000000"), create_test_account(1001, 1001)),
    ];

    // Insert accounts and verify they don't exist before insertion
    for (address, account) in &test_cases {
        let path = AddressPath::for_address(*address);

        let read_account = storage_engine.get_account(&mut context, &path).unwrap();
        assert_eq!(read_account, None);

        storage_engine
            .set_values(&mut context, vec![(path.into(), Some(account.clone().into()))].as_mut())
            .unwrap();
    }

    // Verify all accounts exist after insertion
    for (address, account) in &test_cases {
        let read_account =
            storage_engine.get_account(&mut context, &AddressPath::for_address(*address)).unwrap();
        assert_eq!(read_account, Some(account.clone()));
    }

    // Delete all accounts
    for (address, _) in &test_cases {
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(*address).into(), None)].as_mut(),
            )
            .unwrap();
    }

    // Verify that the accounts don't exist anymore
    for (address, _) in &test_cases {
        let read_account =
            storage_engine.get_account(&mut context, &AddressPath::for_address(*address)).unwrap();
        assert_eq!(read_account, None);
    }
}

#[test]
fn test_some_delete_accounts() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let test_cases = vec![
        (address!("0x4200000000000000000000000000000000000015"), create_test_account(123, 456)),
        (address!("0x4200000000000000000000000000000000000016"), create_test_account(999, 999)),
        (address!("0x4200000000000000000000000000000000000002"), create_test_account(1000, 1000)),
        (address!("0x4200000000000000000000000000000000000000"), create_test_account(1001, 1001)),
    ];

    // Insert accounts and verify they don't exist before insertion
    for (address, account) in &test_cases {
        let path = AddressPath::for_address(*address);

        let read_account = storage_engine.get_account(&mut context, &path).unwrap();
        assert_eq!(read_account, None);

        storage_engine
            .set_values(&mut context, vec![(path.into(), Some(account.clone().into()))].as_mut())
            .unwrap();
    }

    // Verify all accounts exist after insertion
    for (address, account) in &test_cases {
        let read_account =
            storage_engine.get_account(&mut context, &AddressPath::for_address(*address)).unwrap();
        assert_eq!(read_account, Some(account.clone()));
    }

    // Delete only a portion of the accounts
    for (address, _) in &test_cases[0..2] {
        storage_engine
            .set_values(
                &mut context,
                vec![(AddressPath::for_address(*address).into(), None)].as_mut(),
            )
            .unwrap();
    }

    // Verify that the accounts don't exist anymore
    for (address, _) in &test_cases[0..2] {
        let read_account =
            storage_engine.get_account(&mut context, &AddressPath::for_address(*address)).unwrap();
        assert_eq!(read_account, None);
    }

    // Verify that the non-deleted accounts still exist
    for (address, account) in &test_cases[2..] {
        let read_account =
            storage_engine.get_account(&mut context, &AddressPath::for_address(*address)).unwrap();
        assert_eq!(read_account, Some(account.clone()));
    }
}

#[test]
fn test_delete_storage() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let test_cases = vec![
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
            b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
            b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
            b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
            b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
        ),
    ];

    // Insert storage slots and verify they don't exist before insertion
    for (storage_key, storage_value) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(read_storage_slot, None);

        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

        storage_engine
            .set_values(
                &mut context,
                vec![(storage_path.into(), Some(storage_value.into()))].as_mut(),
            )
            .unwrap();
    }

    // Verify that we get all the storage values
    for (storage_key, storage_value) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(read_storage_slot, Some(storage_value));
    }

    // Verify our storage root with alloy
    let mut keys_values: Vec<(B256, U256)> = test_cases
        .clone()
        .into_iter()
        .map(|(key, value)| (key, U256::from_be_bytes::<32>(value.as_slice().try_into().unwrap())))
        .collect();
    let expected_root = storage_root_unhashed(keys_values.clone());
    let account = storage_engine
        .get_account(&mut context, &AddressPath::for_address(address))
        .unwrap()
        .unwrap();

    assert_eq!(account.storage_root, expected_root);

    // Delete storage one at a time
    for (storage_key, _) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        storage_engine
            .set_values(&mut context, vec![(storage_path.clone().into(), None)].as_mut())
            .unwrap();

        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();

        assert_eq!(read_storage_slot, None);

        // check that the storage root is consistent
        keys_values.remove(0);
        let expected_root = storage_root_unhashed(keys_values.clone());
        let account = storage_engine
            .get_account(&mut context, &AddressPath::for_address(address))
            .unwrap()
            .unwrap();

        assert_eq!(account.storage_root, expected_root);
    }
}

#[test]
fn test_delete_account_also_deletes_storage() {
    let (storage_engine, mut context) = create_test_engine(300);

    let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let test_cases = vec![
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000"),
            b256!("0x0000000000000000000000000000000000000000000000000000000062617365"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000002"),
            b256!("0x0000000000000000000000000000000000000000000000000000747269656462"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
            b256!("0x000000000000000000000000000000006274632040202439362c3434322e3735"),
        ),
        (
            // storage key and storage value
            b256!("0x0000000000000000000000000000000000000000000000000000000000000003"),
            b256!("0x000000000000000000000000000000000000000000000000436f696e62617365"),
        ),
    ];

    // Insert storage slots and verify they don't exist before insertion
    for (storage_key, storage_value) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(read_storage_slot, None);

        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

        storage_engine
            .set_values(
                &mut context,
                vec![(storage_path.into(), Some(storage_value.into()))].as_mut(),
            )
            .unwrap();
    }

    // Verify that we get all the storage values
    for (storage_key, storage_value) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        let storage_value = StorageValue::from_be_slice(storage_value.as_slice());

        let read_storage_slot = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(read_storage_slot, Some(storage_value));
    }

    // Delete the account
    storage_engine
        .set_values(&mut context, vec![(AddressPath::for_address(address).into(), None)].as_mut())
        .unwrap();

    // Verify the account no longer exists
    let res = storage_engine.get_account(&mut context, &AddressPath::for_address(address)).unwrap();
    assert_eq!(res, None);

    // Verify all the storage slots don't exist
    for (storage_key, _) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        let res = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(res, None);
    }

    // Now create a new account with the same address again and set storage
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();

    // Verify all the storage slots still don't exist
    for (storage_key, _) in &test_cases {
        let storage_path = StoragePath::for_address_and_slot(address, *storage_key);

        let read_storage = storage_engine.get_storage(&mut context, &storage_path).unwrap();
        assert_eq!(read_storage, None);
    }
}

#[test]
fn test_delete_single_child_branch_on_same_page() {
    let (storage_engine, mut context) = create_test_engine(300);

    // GIVEN: a branch node with 2 children, where all the children live on the same page
    let mut account_1_nibbles = [0u8; 64];
    account_1_nibbles[0] = 1;

    let mut account_2_nibbles = [0u8; 64];
    account_2_nibbles[0] = 11;

    let account1 = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(
                AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)).into(),
                Some(account1.clone().into()),
            )]
            .as_mut(),
        )
        .unwrap();

    let account2 = create_test_account(101, 2);
    storage_engine
        .set_values(
            &mut context,
            vec![(
                AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)).into(),
                Some(account2.clone().into()),
            )]
            .as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let page = storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let slotted_page = SlottedPage::try_from(page).unwrap();
    let node: Node = slotted_page.get_value(0).unwrap();
    assert!(node.is_branch());

    // WHEN: one of these accounts is deleted
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)).into(), None)]
                .as_mut(),
        )
        .unwrap();

    // THEN: the root node should be a leaf node containing the remaining account
    //
    // first verify the deleted account is gone and the remaining account exists
    let read_account1 = storage_engine
        .get_account(&mut context, &AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)))
        .unwrap();
    assert_eq!(read_account1, None);

    let read_account2 = storage_engine
        .get_account(&mut context, &AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)))
        .unwrap();
    assert_eq!(read_account2, Some(account2));

    // check the the root node is a leaf
    let page = storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let slotted_page = SlottedPage::try_from(page).unwrap();
    let node: Node = slotted_page.get_value(0).unwrap();
    assert!(!node.is_branch());
}

#[test]
fn test_delete_single_child_non_root_branch_on_different_pages() {
    let (storage_engine, mut context) = create_test_engine(300);

    // GIVEN: a non-root branch node with 2 children where both children are on a different
    // pages
    //
    // first we construct a root branch node.
    let mut account_1_nibbles = [0u8; 64];
    account_1_nibbles[0] = 1;

    let mut account_2_nibbles = [0u8; 64];
    account_2_nibbles[0] = 11;

    let account1 = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(
                AddressPath::new(Nibbles::from_nibbles(account_1_nibbles)).into(),
                Some(account1.clone().into()),
            )]
            .as_mut(),
        )
        .unwrap();

    let account2 = create_test_account(101, 2);
    storage_engine
        .set_values(
            &mut context,
            vec![(
                AddressPath::new(Nibbles::from_nibbles(account_2_nibbles)).into(),
                Some(account2.clone().into()),
            )]
            .as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));

    let page = storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let slotted_page = SlottedPage::try_from(page).unwrap();
    let mut root_node: Node = slotted_page.get_value(0).unwrap();
    assert!(root_node.is_branch());

    let test_account = create_test_account(424, 234);

    // next we will force add a branch node in the middle of the root node (index 5)

    // page1 will hold our root node and the branch node
    let page1 = storage_engine.get_mut_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let mut slotted_page1 = SlottedPageMut::try_from(page1).unwrap();

    // page2 will hold our 1st child
    let page2 = storage_engine.allocate_page(&mut context).unwrap();
    let mut slotted_page2 = SlottedPageMut::try_from(page2).unwrap();

    // page3 will hold our 2nd child
    let page3 = storage_engine.allocate_page(&mut context).unwrap();
    let mut slotted_page3 = SlottedPageMut::try_from(page3).unwrap();

    // we will force add 2 children to this branch node
    let mut child_1_full_path = [0u8; 64];
    child_1_full_path[0] = 5; // root branch nibble
    child_1_full_path[1] = 0; // inner branch nibble
    child_1_full_path[2] = 10; // leaf prefix
    child_1_full_path[3] = 11; // leaf prefix
    child_1_full_path[4] = 12; // leaf prefix
    let child_1: Node = Node::new_leaf(
        &RawPath::from_nibbles(&child_1_full_path[2..]),
        &TrieValue::Account(test_account.clone()),
    )
    .expect("can create node");

    let mut child_2_full_path = [0u8; 64];
    child_2_full_path[0] = 5; // root branch nibble
    child_2_full_path[1] = 15; // inner branch nibble
    child_2_full_path[2] = 1; // leaf prefix
    child_2_full_path[3] = 2; // leaf prefix
    child_2_full_path[4] = 3; // leaf prefix
    let child_2: Node = Node::new_leaf(
        &RawPath::from_nibbles(&child_2_full_path[2..]),
        &TrieValue::Account(test_account.clone()),
    )
    .expect("can create node");

    // child 1 is the root of page2
    slotted_page2.insert_value(&child_1).unwrap();
    let child_1_location = Location::from(slotted_page2.id());

    // child 2 is the root of page3
    slotted_page3.insert_value(&child_2).unwrap();
    let child_2_location = Location::from(slotted_page3.id());

    let mut new_branch_node: Node = Node::new_branch(&RawPath::new()).expect("can create node");
    new_branch_node
        .set_child(0, Pointer::new(child_1_location, RlpNode::default()))
        .expect("can set child");
    new_branch_node
        .set_child(15, Pointer::new(child_2_location, RlpNode::default()))
        .expect("can set child");
    let new_branch_node_index = slotted_page1.insert_value(&new_branch_node).unwrap();
    let new_branch_node_location = Location::from(new_branch_node_index as u32);

    root_node
        .set_child(5, Pointer::new(new_branch_node_location, RlpNode::default()))
        .expect("can set child");
    slotted_page1.set_value(0, &root_node).unwrap();

    drop(slotted_page1);
    drop(slotted_page2);
    let slotted_page3 = slotted_page3.downcast();
    storage_engine.commit(&context).unwrap();

    // assert we can get the child account we just added:
    let child_1_nibbles = Nibbles::from_nibbles(child_1_full_path);
    let child_2_nibbles = Nibbles::from_nibbles(child_2_full_path);
    let read_account1 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_1_nibbles)).unwrap();
    assert_eq!(read_account1, Some(test_account.clone()));
    let read_account2 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_2_nibbles)).unwrap();
    assert_eq!(read_account2, Some(test_account.clone()));

    // WHEN: child 1 is deleted
    let child_1_path = Nibbles::from_nibbles(child_1_full_path);
    storage_engine
        .set_values(&mut context, vec![(AddressPath::new(child_1_path).into(), None)].as_mut())
        .unwrap();

    // THEN: the branch node should be deleted and the root node should go to child 2 leaf at
    // index 5
    let root_node: Node = slotted_page.get_value(0).unwrap();
    assert!(root_node.is_branch());
    let child_2_pointer = root_node.child(5).expect("can get child").unwrap();
    assert!(child_2_pointer.location().page_id().is_some());
    assert_eq!(child_2_pointer.location().page_id().unwrap(), slotted_page3.id());

    // check that the prefix for child 2 has changed
    let child_2_node: Node = slotted_page3.get_value(0).unwrap();
    assert!(!child_2_node.is_branch());
    assert_eq!(child_2_node.prefix().clone(), Nibbles::from_nibbles(&child_2_full_path[1..]));

    // test that we can get child 2 and not child 1
    let read_account2 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_2_nibbles)).unwrap();
    assert_eq!(read_account2, Some(test_account.clone()));
    let read_account1 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_1_nibbles)).unwrap();
    assert_eq!(read_account1, None);
}

#[test]
fn test_delete_single_child_root_branch_on_different_pages() {
    let (storage_engine, mut context) = create_test_engine(300);

    // GIVEN: a root branch node with 2 children where both children are on a different page
    //
    // first we construct our two children on separate pages.
    let test_account = create_test_account(424, 234);

    // page2 will hold our 1st child
    let page2 = storage_engine.allocate_page(&mut context).unwrap();
    let mut slotted_page2 = SlottedPageMut::try_from(page2).unwrap();

    // page3 will hold our 2nd child
    let page3 = storage_engine.allocate_page(&mut context).unwrap();
    let mut slotted_page3 = SlottedPageMut::try_from(page3).unwrap();

    // we will force add 2 children to our root node
    let mut child_1_full_path = [0u8; 64];
    child_1_full_path[0] = 0; // root branch nibble
    child_1_full_path[2] = 10; // leaf prefix
    child_1_full_path[3] = 11; // leaf prefix
    child_1_full_path[4] = 12; // leaf prefix
    let child_1: Node = Node::new_leaf(
        &RawPath::from_nibbles(&child_1_full_path[1..]),
        &TrieValue::Account(test_account.clone()),
    )
    .expect("can create node");

    let mut child_2_full_path = [0u8; 64];
    child_2_full_path[0] = 15; // root branch nibble
    child_2_full_path[2] = 1; // leaf prefix
    child_2_full_path[3] = 2; // leaf prefix
    child_2_full_path[4] = 3; // leaf prefix
    let child_2: Node = Node::new_leaf(
        &RawPath::from_nibbles(&child_2_full_path[1..]),
        &TrieValue::Account(test_account.clone()),
    )
    .expect("can create node");

    // child 1 is the root of page2
    slotted_page2.insert_value(&child_1).unwrap();
    let child_1_location = Location::from(slotted_page2.id());

    // child 2 is the root of page3
    slotted_page3.insert_value(&child_2).unwrap();
    let child_2_location = Location::from(slotted_page3.id());

    // next we create and update our root node
    let mut root_node = Node::new_branch(&RawPath::new()).expect("can create node");
    root_node
        .set_child(0, Pointer::new(child_1_location, RlpNode::default()))
        .expect("can set child");
    root_node
        .set_child(15, Pointer::new(child_2_location, RlpNode::default()))
        .expect("can set child");

    let root_node_page = storage_engine.allocate_page(&mut context).unwrap();
    context.root_node_page_id = Some(root_node_page.id());
    let mut slotted_page = SlottedPageMut::try_from(root_node_page).unwrap();
    let root_index = slotted_page.insert_value(&root_node).unwrap();
    assert_eq!(root_index, 0);

    drop(slotted_page);
    drop(slotted_page2);
    drop(slotted_page3);

    // not necessary but let's commit our changes.
    storage_engine.commit(&context).unwrap();

    // assert we can get the children accounts we just added:
    let child_1_nibbles = Nibbles::from_nibbles(child_1_full_path);
    let child_2_nibbles = Nibbles::from_nibbles(child_2_full_path);
    let read_account1 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_1_nibbles)).unwrap();
    assert_eq!(read_account1, Some(test_account.clone()));
    let read_account2 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_2_nibbles)).unwrap();
    assert_eq!(read_account2, Some(test_account.clone()));

    // WHEN: child 1 is deleted
    storage_engine
        .set_values(&mut context, vec![(AddressPath::new(child_1_nibbles).into(), None)].as_mut())
        .unwrap();

    // THEN: the root branch node should be deleted and the root node should be the leaf of
    // child 2 on the child's page
    let root_node_page =
        storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let root_node_slotted = SlottedPage::try_from(root_node_page).unwrap();
    let root_node: Node = root_node_slotted.get_value(0).unwrap();
    assert!(!root_node.is_branch());
    assert_eq!(root_node_slotted.id(), child_2_location.page_id().unwrap());

    // check that the prefix for root node has changed
    assert_eq!(root_node.prefix().clone(), child_2_nibbles);

    // test that we can get child 2 and not child 1
    let read_account2 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_2_nibbles)).unwrap();
    assert_eq!(read_account2, Some(test_account.clone()));
    let read_account1 =
        storage_engine.get_account(&mut context, &AddressPath::new(child_1_nibbles)).unwrap();
    assert_eq!(read_account1, None);
}

#[test]
fn test_delete_non_existent_value_doesnt_change_trie_structure() {
    let (storage_engine, mut context) = create_test_engine(300);

    // GIVEN: a trie with a single account
    let address_nibbles =
        Nibbles::unpack(hex!("0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7a5c971e1c3e85ea62492"));
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::new(address_nibbles).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    assert_eq!(context.root_node_page_id, Some(page_id!(1)));
    let root_subtrie_page =
        storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let root_subtrie_contents_before = root_subtrie_page.contents().to_vec();

    // WHEN: an account with a similar but divergent path is deleted
    let address_nibbles =
        Nibbles::unpack(hex!("0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7ffffffffffffffffffff"));
    storage_engine
        .set_values(&mut context, vec![(AddressPath::new(address_nibbles).into(), None)].as_mut())
        .unwrap();

    // THEN: the trie should remain unchanged
    let root_subtrie_page =
        storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let root_subtrie_contents_after = root_subtrie_page.contents().to_vec();
    assert_eq!(root_subtrie_contents_before, root_subtrie_contents_after);

    //**Additional Test**//

    // GIVEN: a trie with a branch node
    let address = address!("0xe8da6bf26964af9d7eed9e03e53415d37aa96045"); // first nibble is different, hash should force a branch node
    storage_engine
        .set_values(
            &mut context,
            vec![(AddressPath::for_address(address).into(), Some(account.clone().into()))].as_mut(),
        )
        .unwrap();
    let root_node_page =
        storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let root_subtrie_contents_before = root_node_page.contents().to_vec();
    let root_node_slotted_page = SlottedPage::try_from(root_node_page).unwrap();
    let root_node: Node = root_node_slotted_page.get_value(0).unwrap();
    assert!(root_node.is_branch());

    // WHEN: a non-existent value is deleted from the branch node
    let address = address!("0xf8da6bf26964af9d7eed9e03e53415d37aa96045"); // first nibble is different, hash doesn't exist
    storage_engine
        .set_values(&mut context, vec![(AddressPath::for_address(address).into(), None)].as_mut())
        .unwrap();

    // THEN: the trie should remain unchanged
    let root_subtrie_page =
        storage_engine.get_page(&context, context.root_node_page_id.unwrap()).unwrap();
    let root_subtrie_contents_after = root_subtrie_page.contents().to_vec();
    assert_eq!(root_subtrie_contents_before, root_subtrie_contents_after);
}

#[test]
fn test_leaf_update_and_non_existent_delete_works() {
    let (storage_engine, mut context) = create_test_engine(300);

    // GIVEN: a trie with a single account
    let address_nibbles_original_account =
        Nibbles::unpack(hex!("0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7a5c971e1c3e85ea62492"));
    let account = create_test_account(100, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![(
                AddressPath::new(address_nibbles_original_account).into(),
                Some(account.clone().into()),
            )]
            .as_mut(),
        )
        .unwrap();

    // WHEN: the same account is modified alongside a delete operation of a non existent value
    let address_nibbles =
        Nibbles::unpack(hex!("0xf80f21938e5248ec70b870ac1103d0dd01b7811550a7ffffffffffffffffffff"));

    let updated_account = create_test_account(300, 1);
    storage_engine
        .set_values(
            &mut context,
            vec![
                (
                    AddressPath::new(address_nibbles_original_account).into(),
                    Some(updated_account.clone().into()),
                ),
                (AddressPath::new(address_nibbles).into(), None),
            ]
            .as_mut(),
        )
        .unwrap();

    // THEN: the updated account should be updated
    let account_in_database = storage_engine
        .get_account(&mut context, &AddressPath::new(address_nibbles_original_account))
        .unwrap()
        .unwrap();
    assert_eq!(account_in_database, updated_account);
}

fn address_path_for_idx(idx: u64) -> AddressPath {
    let mut nibbles = [0u8; 64];
    let mut val = idx;
    let mut pos = 63;
    while val > 0 {
        nibbles[pos] = (val % 16) as u8;
        val /= 16;
        pos -= 1;
    }
    AddressPath::new(Nibbles::from_nibbles(nibbles))
}

proptest! {
    #[test]
    fn fuzz_insert_get_accounts(
        accounts in prop::collection::vec(
            (any::<Address>(), any::<Account>()),
            1..100
        )
    ) {
        let (storage_engine, mut context) = create_test_engine(10_000);

        for (address, account) in &accounts {
            storage_engine
                .set_values(&mut context, vec![(AddressPath::for_address(*address).into(), Some(account.clone().into()))].as_mut())
                .unwrap();
        }

        for (address, account) in accounts {
            let read_account = storage_engine
                .get_account(&mut context, &AddressPath::for_address(address))
                .unwrap();
            assert_eq!(read_account, Some(Account::new(account.nonce, account.balance, EMPTY_ROOT_HASH, account.code_hash)));
        }
    }

    #[test]
    fn fuzz_insert_get_accounts_and_storage(
        accounts in prop::collection::vec(
            (any::<Address>(), any::<Account>(), prop::collection::vec(
                (any::<B256>(), any::<U256>()),
                0..5
            )),
            1..100
        ),
    ) {
        let (storage_engine, mut context) = create_test_engine(10_000);

        let mut changes = vec![];
        for (address, account, storage) in &accounts {
            changes.push((AddressPath::for_address(*address).into(), Some(account.clone().into())));

            for (key, value) in storage {
                changes.push((StoragePath::for_address_and_slot(*address, *key).into(), Some((*value).into())));
            }
        }
        storage_engine
            .set_values(&mut context, changes.as_mut())
            .unwrap();

        for (address, account, storage) in accounts {
            let read_account = storage_engine
                .get_account(&mut context, &AddressPath::for_address(address))
                .unwrap();
            let read_account = read_account.unwrap();
            assert_eq!(read_account.nonce, account.nonce);
            assert_eq!(read_account.balance, account.balance);
            assert_eq!(read_account.code_hash, account.code_hash);

            for (key, value) in storage {
                let read_storage = storage_engine
                    .get_storage(&mut context, &StoragePath::for_address_and_slot(address, key))
                    .unwrap();
                assert_eq!(read_storage, Some(value));
            }
        }
    }

    #[test]
    fn fuzz_insert_update_accounts(
        account_revisions in prop::collection::vec(
            (any::<Address>(), prop::collection::vec(any::<Account>(), 1..100)),
            1..100
        ),
    ) {
        let (storage_engine, mut context) = create_test_engine(10_000);

        let mut revision = 0;
        loop {
            let mut changes = vec![];
            for (address, revisions) in &account_revisions {
                if revisions.len() > revision {
                    changes.push((AddressPath::for_address(*address).into(), Some(revisions[revision].clone().into())));
                }
            }
            if changes.is_empty() {
                break;
            }
            storage_engine
                .set_values(&mut context, changes.as_mut())
                .unwrap();
            revision += 1;
        }

        for (address, revisions) in &account_revisions {
            let last_revision = revisions.last().unwrap();
            let read_account = storage_engine
                .get_account(&mut context, &AddressPath::for_address(*address))
                .unwrap();
            let read_account = read_account.unwrap();
            assert_eq!(read_account.nonce, last_revision.nonce);
            assert_eq!(read_account.balance, last_revision.balance);
            assert_eq!(read_account.code_hash, last_revision.code_hash);
        }
    }

    #[test]
    fn fuzz_find_shortest_common_prefix(
        mut changes in prop::collection::vec(
            (any::<RawPath>(), any::<bool>()),
            1..10
        ),
        node in any::<Node>(),
    ) {
        changes.sort_by(|a, b| a.0.cmp(&b.0));
        let (idx, shortest_common_prefix_length) = find_shortest_common_prefix(&changes, 0, &node);
        assert!(idx == 0 || idx == changes.len() - 1, "the shortest common prefix must be found at either end of the changes list");

        let prefix: RawPath = node.prefix().into();
        let shortest_from_full_iteration = changes.iter().map(|(path, _)| path.common_prefix_length(&prefix)).min().unwrap();

        assert_eq!(shortest_common_prefix_length, shortest_from_full_iteration);
    }
}

#[test]
fn test_double_orphan_bug_repro() {
    let (storage_engine, mut context) = create_test_engine(10_000);

    // Step 1: Create a target account that will live alone on its own page
    let target_address = address!("1111111111111111111111111111111111111111");
    let target_account = create_test_account(1, 100);

    // Allocate a dedicated page for our target account (this will be page 1)
    let target_page = storage_engine.allocate_page(&mut context).unwrap();
    let target_page_id = target_page.id();
    let mut target_slotted_page = SlottedPageMut::try_from(target_page).unwrap();

    // Create the target account node and insert it at index 0 (root of the page)
    let target_path = AddressPath::for_address(target_address);
    let target_node = Node::new_leaf(
        &RawPath::from(&target_path).slice(1..),
        &TrieValue::Account(target_account.clone()),
    )
    .unwrap();
    let target_node_index = target_slotted_page.insert_value(&target_node).unwrap();
    assert_eq!(target_node_index, 0, "Target node should be at root of its page");

    drop(target_slotted_page); // Release the page

    // Step 2: Create a parent branch node on a different page that points to our target
    let parent_page = storage_engine.allocate_page(&mut context).unwrap();
    let parent_page_id = parent_page.id();
    context.root_node_page_id = Some(parent_page_id); // Make this the root
    let mut parent_slotted_page = SlottedPageMut::try_from(parent_page).unwrap();

    // Create a branch node with a short prefix that will point to our target
    let mut parent_branch = Node::new_branch(&RawPath::new()).unwrap();

    // Set the target as a child of the parent branch
    // Use the first nibble of the target address to determine the branch index
    let target_nibbles = RawPath::from(&target_path);
    let branch_index = target_nibbles.get_unchecked(0);

    // Create a pointer to the target node with the remaining path
    let remaining_path = target_nibbles.slice(1..);
    let target_node_for_pointer =
        Node::new_leaf(&remaining_path, &TrieValue::Account(target_account.clone())).unwrap();
    let target_pointer_with_path =
        Pointer::new(Location::from(target_page_id), target_node_for_pointer.to_rlp_node());

    parent_branch.set_child(branch_index, target_pointer_with_path).unwrap();

    // Insert the parent branch at index 0 (root of parent page)
    let parent_node_index = parent_slotted_page.insert_value(&parent_branch).unwrap();
    assert_eq!(parent_node_index, 0, "Parent branch should be at root of its page");

    drop(parent_slotted_page); // Release the page

    // Step 3: Commit this initial state to establish baseline snapshots
    storage_engine.commit(&context).unwrap();
    context = storage_engine.write_context();

    // Step 4: Count orphan pages before the delete operation
    let orphan_count_before = {
        let mut meta_manager = storage_engine.meta_manager.lock();
        meta_manager.orphan_pages().len()
    };
    assert_eq!(orphan_count_before, 0, "Expected no orphan pages before the delete operation");

    // Step 5: Delete the target account, causing the parent and target pages to be orphaned, as
    // well as their mutable clones. Both pages should be cloned as they are iterated
    // over, but then the clones should be deleted in the cleanup phase as their
    // root nodes are deleted.
    storage_engine.set_values(&mut context, vec![(target_path.into(), None)].as_mut()).unwrap();

    // Step 6: Check for duplicate orphan entries
    let mut meta_manager = storage_engine.meta_manager.lock();
    let orphan_pages = meta_manager.orphan_pages();
    let count = orphan_pages.len();

    // Look for duplicate entries
    let mut orphan_page_ids = HashSet::new();

    for orphan_page in orphan_pages.iter() {
        assert!(
            orphan_page_ids.insert(orphan_page.page_id()),
            "page {} is already in the orphan page list",
            orphan_page.page_id()
        );
    }

    assert!(
        orphan_page_ids.contains(&target_page_id),
        "target page {target_page_id} is not in the orphan page list"
    );
    assert!(
        orphan_page_ids.contains(&parent_page_id),
        "parent page {parent_page_id} is not in the orphan page list"
    );
    assert_eq!(count, 4, "Expected 4 orphan pages after the delete operation");
}
