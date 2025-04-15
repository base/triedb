use alloy_primitives::{keccak256, Address, Bytes, StorageKey, StorageValue, B256, U256, U64};
use alloy_trie::{
    root::{state_root_unhashed, storage_root_unhashed},
    TrieAccount, EMPTY_ROOT_HASH,
};
use serde_json::{Map, Value};
use std::{
    cmp::min,
    collections::{HashMap, HashSet},
    str::FromStr,
    sync::Arc,
};
use tempdir::TempDir;
use triedb::{
    account::Account,
    path::{AddressPath, StoragePath},
    Database,
};
use walkdir::WalkDir;

#[test]
fn run_ethereum_execution_spec_state_tests() {
    for test_spec_entry in
        WalkDir::new("tests/fixtures/state_tests").into_iter().filter_map(Result::ok).filter(|e| {
            e.file_type().is_file() && e.path().extension().is_some_and(|ext| ext == "json")
        })
    {
        let test_file = std::fs::File::open(test_spec_entry.path()).unwrap();
        let state_test_case: Value = serde_json::from_reader(test_file).unwrap();
        let test_cases = state_test_case.as_object().unwrap();
        for (test_case_name, test_case) in test_cases.iter() {
            let tmp_dir = TempDir::new("ethereum_execution_spec_state_tests").unwrap();
            println!("running test: {:?}", test_case_name);
            let database_file_name = &format!("test_db_{}", test_case_name)
                .as_str()
                .replace("/", "_")[0..min(test_case_name.len(), 100)];
            let file_path = tmp_dir.path().join(database_file_name).to_str().unwrap().to_owned();
            let test_database = Arc::new(Database::create(file_path.as_str()).unwrap());

            // will track accounts and storage that need to be deleted. this is essentially the
            // "diff" between the pre state and post state.
            let mut pre_accounts_info: HashMap<Address, HashSet<StorageKey>> = HashMap::new();

            // load the pre state accounts into the database. this isn't necessarily needed
            // but it's nice to test set_value in a populated database
            let mut tx = test_database.begin_rw().unwrap();
            let pre_state = test_case["pre"].as_object().unwrap();
            for (account_address_hex_string, account_state) in pre_state.iter() {
                let alloy_address = Address::from_str(account_address_hex_string).unwrap();
                let balance: U256 = account_state["balance"].as_str().unwrap().parse().unwrap();
                let nonce: U64 = account_state["nonce"].as_str().unwrap().parse().unwrap();
                let code: Bytes = account_state["code"].as_str().unwrap().parse().unwrap();
                let account = Account::new(
                    u64::from_le_bytes(
                        nonce.as_le_slice().try_into().expect("nonce should be 64 bits"),
                    ),
                    balance,
                    EMPTY_ROOT_HASH,
                    keccak256(code),
                );

                tx.set_account(AddressPath::for_address(alloy_address), Some(account)).unwrap();

                let mut storage_set = HashSet::new();

                // add all the storage values for this account
                let storage_map = account_state["storage"].as_object().unwrap();
                for (storage_key_kex_string, storage_json_value) in storage_map.iter() {
                    let storage_key_bytes: Bytes = storage_key_kex_string.parse().unwrap();
                    let storage_key = StorageKey::left_padding_from(&storage_key_bytes);

                    let storage_value_bytes: Bytes =
                        storage_json_value.as_str().unwrap().parse().unwrap();
                    let storage_value: StorageValue =
                        B256::left_padding_from(&storage_value_bytes).into();

                    tx.set_storage_slot(
                        StoragePath::for_address_and_slot(alloy_address, storage_key),
                        Some(storage_value),
                    )
                    .unwrap();

                    storage_set.insert(storage_key);
                }

                pre_accounts_info.insert(alloy_address, storage_set.clone());
            }
            tx.commit().unwrap();

            let mut tx = test_database.begin_rw().unwrap();
            let post_state = test_case["post"].as_object().unwrap();
            assert_eq!(post_state.len(), 1);
            let mut expected_state_root: B256 = EMPTY_ROOT_HASH;
            for (_, fork_post_state_list) in post_state.iter() {
                let post_state_data =
                    fork_post_state_list.as_array().unwrap()[0].as_object().unwrap();
                expected_state_root = post_state_data["hash"].as_str().unwrap().parse().unwrap();

                let updated_accounts = post_state_data["state"].as_object().unwrap();
                for (account_address_hex_string, updated_account_state) in updated_accounts.iter() {
                    let alloy_address = Address::from_str(account_address_hex_string).unwrap();
                    let balance: U256 =
                        updated_account_state["balance"].as_str().unwrap().parse().unwrap();
                    let nonce: U64 =
                        updated_account_state["nonce"].as_str().unwrap().parse().unwrap();
                    let code: Bytes =
                        updated_account_state["code"].as_str().unwrap().parse().unwrap();
                    let account = Account::new(
                        u64::from_le_bytes(
                            nonce.as_le_slice().try_into().expect("nonce should be 64 bits"),
                        ),
                        balance,
                        EMPTY_ROOT_HASH,
                        keccak256(code),
                    );

                    tx.set_account(AddressPath::for_address(alloy_address), Some(account)).unwrap();

                    let mut storage_set =
                        pre_accounts_info.get(&alloy_address).cloned().unwrap_or_default();

                    // add all the new storage values for this account
                    let storage_map = updated_account_state["storage"].as_object().unwrap();
                    for (storage_key_kex_string, storage_json_value) in storage_map.iter() {
                        let storage_key_bytes: Bytes = storage_key_kex_string.parse().unwrap();
                        let storage_key = StorageKey::left_padding_from(&storage_key_bytes);

                        let storage_value_bytes: Bytes =
                            storage_json_value.as_str().unwrap().parse().unwrap();
                        let storage_value: StorageValue =
                            B256::left_padding_from(&storage_value_bytes).into();

                        tx.set_storage_slot(
                            StoragePath::for_address_and_slot(alloy_address, storage_key),
                            Some(storage_value),
                        )
                        .unwrap();

                        storage_set.remove(&storage_key);
                    }

                    // remove all storage that existed in the pre-state but no longer exists
                    // in the post state
                    for storage_key_to_remove in storage_set.iter() {
                        tx.set_storage_slot(
                            StoragePath::for_address_and_slot(
                                alloy_address,
                                *storage_key_to_remove,
                            ),
                            None,
                        )
                        .unwrap();
                    }

                    // the account exists in the post state so remove it.
                    pre_accounts_info.remove(&alloy_address);
                }

                // remove all accounts that existed in the pre-state but no longer exists
                // in the post-state
                for account_to_remove in pre_accounts_info.keys() {
                    tx.set_account(AddressPath::for_address(*account_to_remove), None).unwrap();
                }
            }
            tx.commit().unwrap();

            assert_eq!(
                expected_state_root,
                test_database.state_root(),
                "failed test: {}",
                test_case_name
            );

            tmp_dir.close().unwrap();
        }
    }
}

#[allow(dead_code)]
// useful for debugging root hashes using alloy trie
fn get_state_root_and_account_storage_roots_with_alloy_trie(
    post_state_data: Map<String, Value>,
) -> (B256, HashMap<Address, B256>) {
    let updated_accounts = post_state_data["state"].as_object().unwrap();
    let mut accounts: Vec<(Address, TrieAccount)> = Vec::new();
    let mut account_storage_roots = HashMap::new();
    for (account_address_hex_string, updated_account_state) in updated_accounts.iter() {
        let mut storage: Vec<(StorageKey, StorageValue)> = Vec::new();

        let alloy_address = Address::from_str(account_address_hex_string).unwrap();
        let storage_map = updated_account_state["storage"].as_object().unwrap();

        for (storage_key_kex_string, storage_json_value) in storage_map.iter() {
            let storage_key_bytes: Bytes = storage_key_kex_string.parse().unwrap();
            let storage_key = StorageKey::left_padding_from(&storage_key_bytes);

            let storage_value_bytes: Bytes = storage_json_value.as_str().unwrap().parse().unwrap();
            let storage_value: StorageValue = B256::left_padding_from(&storage_value_bytes).into();

            storage.push((storage_key, storage_value))
        }

        let alloy_storage_root = storage_root_unhashed(storage.clone().into_iter());
        account_storage_roots.insert(alloy_address, alloy_storage_root);

        let alloy_address = Address::from_str(account_address_hex_string).unwrap();
        let balance: U256 = updated_account_state["balance"].as_str().unwrap().parse().unwrap();
        let nonce: U64 = updated_account_state["nonce"].as_str().unwrap().parse().unwrap();
        let code: Bytes = updated_account_state["code"].as_str().unwrap().parse().unwrap();

        let account = TrieAccount {
            nonce: u64::from_le_bytes(
                nonce.as_le_slice().try_into().expect("nonce should be 64 bits"),
            ),
            balance,
            storage_root: alloy_storage_root,
            code_hash: keccak256(code),
        };

        accounts.push((alloy_address, account));
    }

    (state_root_unhashed(accounts.clone()), account_storage_roots)
}
