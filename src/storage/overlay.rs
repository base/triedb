use crate::{
    context::TransactionContext,
    overlay::OverlayState,
    path::{AddressPath, RawPath, StoragePath},
    storage::{
        proofs::AccountProof,
        engine::{Error, StorageEngine},
        overlay_traversal::OverlayTrie
    },
};
use alloy_primitives::{map::{HashMap, B256Map}, B256};
use alloy_trie::{Nibbles, BranchNodeCompact};
use std::collections::HashSet;

/// Represents the result of applying an overlay to the state root.
/// Contains the new root hash and any updated branch nodes.
#[derive(Debug)]
pub struct OverlayedRoot {
    pub root: B256,
    pub updated_branch_nodes: HashMap<Nibbles, BranchNodeCompact>,
    pub storage_branch_updates: B256Map<HashMap<Nibbles, BranchNodeCompact>>,
}

impl OverlayedRoot {
    pub fn new(
        root: B256,
        updated_branch_nodes: HashMap<Nibbles, BranchNodeCompact>,
        storage_branch_updates: B256Map<HashMap<Nibbles, BranchNodeCompact>>,
    ) -> Self {
        Self { root, updated_branch_nodes, storage_branch_updates }
    }

    pub fn new_hash(root: B256) -> Self {
        Self {
            root,
            updated_branch_nodes: HashMap::default(),
            storage_branch_updates: B256Map::default(),
        }
    }
}

impl StorageEngine {
    /// Creates an `OverlayTrie` builder for applying overlay state to the persistent trie.
    ///
    /// This is a low-level builder that allows fine-grained control over the overlay
    /// traversal process, including specifying proof targets. For most use cases,
    /// prefer the higher-level methods like `compute_state_root_with_overlay()`,
    /// `compute_account_with_proof_with_overlay()` or `compute_storage_with_proof_with_overlay()`.
    ///
    /// # Arguments
    /// * `context` - Transaction context containing the base state
    /// * `overlay` - Overlay state containing pending modifications
    ///
    /// # Returns
    /// An `OverlayTrie` builder that can be configured and executed
    ///
    /// # Example
    /// ```ignore
    /// let trie = engine.overlay_trie(context, overlay)
    ///     .with_proof_targets(targets)
    ///     .compute_root()?;
    /// ```
    pub fn overlay_trie<'a>(
        &'a self,
        context: &'a TransactionContext,
        overlay: OverlayState,
    ) -> OverlayTrie<'a> {
        OverlayTrie::new(self, context, overlay)
    }

    /// Computes a new state root by applying overlay state to the persistent trie.
    ///
    /// This method merges the uncommitted overlay state with the persistent storage
    /// to compute the resulting state root hash.
    /// 
    /// # Arguments
    /// * `context` - Transaction context containing the base state root
    /// * `overlay` - Overlay state containing pending account/storage modifications
    ///
    /// # Returns
    /// * `Ok(OverlayedRoot)` - Contains the new root hash and updated branch nodes
    /// * `Err(Error)` - If an error occurs during traversal or hashing
    pub fn compute_state_root_with_overlay(
        &self,
        context: &TransactionContext,
        overlay: OverlayState,
    ) -> Result<OverlayedRoot, Error> {
        if overlay.is_empty() {
            return Ok(OverlayedRoot::new_hash(context.root_node_hash));
        }

        self.overlay_trie(context, overlay).compute_root()
    }

    /// Computes an account proof for the given address by applying overlay state to the persistent trie.
    ///
    /// This method merges the uncommitted overlay state with the persistent storage 
    /// to compute the account proof.
    /// 
    /// # Arguments
    /// * `context` - Transaction context containing the base state
    /// * `address_path` - Path to the account address
    /// * `overlay` - Overlay state containing pending modifications
    ///
    /// # Returns
    /// * `Ok(Some(AccountProof))` - If the account exists in base state or overlay
    /// * `Ok(None)` - If the account doesn't exist (was tombstoned)
    /// * `Err(Error)` - If an error occurred during proof generation
    pub fn compute_account_with_proof_with_overlay(
        &self,
        context: &TransactionContext,
        address_path: AddressPath,
        overlay: OverlayState,
    ) -> Result<Option<AccountProof>, Error> {
        let account_nibbles = Nibbles::from(address_path.clone());
        let mut prover = self
            .overlay_trie(context, overlay)
            .with_proof_targets(HashSet::from([account_nibbles]))
            .compute_proof()?;

        Ok(prover.account_proof(address_path))
    }

    /// Computes both account and storage proofs for the given storage slot by applying overlay state to the persistent trie.
    ///
    /// This method merges the uncommitted overlay state with the persistent storage to compute the proofs.
    ///
    /// # Arguments
    /// * `context` - Transaction context containing the base state
    /// * `storage_path` - Path to the storage slot
    /// * `overlay` - Overlay state containing pending modifications
    ///
    /// # Returns
    /// * `Ok(Some(AccountProof))` - If the account exists, with storage proof included
    /// * `Ok(None)` - If the account doesn't exist
    /// * `Err(Error)` - If an error occurred during proof generation
    pub fn compute_storage_with_proof_with_overlay(
        &self,
        context: &TransactionContext,
        storage_path: StoragePath,
        overlay: OverlayState,
    ) -> Result<Option<AccountProof>, Error> {
        let account_nibbles = Nibbles::from(storage_path.get_address().clone());
        let target_nibbles = HashSet::from([account_nibbles.clone()]);

        let slot_nibbles = storage_path.get_slot().clone();
        let raw_slot_path = RawPath::from(slot_nibbles.clone());
        let mut storage_targets = HashMap::default();
        storage_targets.insert(account_nibbles, HashSet::from([slot_nibbles]));

        let mut prover = self
            .overlay_trie(context, overlay)
            .with_proof_targets(target_nibbles)
            .with_storage_proof_targets(storage_targets)
            .compute_proof()?;

        let account_proof_opt = prover.account_proof(storage_path.get_address().clone());

        if let Some(mut account_proof) = account_proof_opt {
             let storage_proof_opt = prover.storage_proof(storage_path);

             if let Some(storage_proof) = storage_proof_opt {
                account_proof
                    .storage_proofs
                    .insert(B256::from_slice(&raw_slot_path.pack::<32>()), storage_proof);
             }
             Ok(Some(account_proof))
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, B256, U256};
    use alloy_trie::{KECCAK_EMPTY, EMPTY_ROOT_HASH, Nibbles};

    use crate::{
        account::Account, overlay::{OverlayStateMut, OverlayValue},
        path::{AddressPath, RawPath, StoragePath},
        storage::test_utils::{create_test_account, create_test_engine, verify_account_proof},
    };


    #[test]
    fn test_compute_account_from_overlay() {
        let (storage_engine, mut context) = create_test_engine(2000);

        // 1. insert a single account to storage
        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);

        storage_engine
            .set_values(
                &mut context,
                vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        // 2. create overlay with updated account
        let mut overlay_mut = OverlayStateMut::new();
        let new_account = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut.insert(path.clone().into(), Some(OverlayValue::Account(new_account.clone())));
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        let proof = storage_engine.compute_account_with_proof_with_overlay(&context, path.clone(), overlay).unwrap().unwrap();
        assert_eq!(proof.account, new_account);
        
        // The proof logic uses Alloy Trie's HashBuilder proof retention.
        // For a single leaf node, it might generate just the leaf if root is the leaf (small tree).
        // Since we have 1 account in DB and we modify it in overlay, the structure is still 1 node.
        
        verify_account_proof(&proof, overlay_root);
    }

    #[test]
    fn test_compute_account_from_overlay_new_account() {
         let (storage_engine, context) = create_test_engine(2000);
         
         // 1. Storage is empty
         
         // 2. Overlay adds a new account
        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(path.clone().into(), Some(OverlayValue::Account(account.clone())));
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        let proof = storage_engine.compute_account_with_proof_with_overlay(&context, path.clone(), overlay).unwrap().unwrap();
        assert_eq!(proof.account, account);
        
        verify_account_proof(&proof, overlay_root);
    }

    #[test]
    fn test_compute_account_from_overlay_tombstone() {
        let (storage_engine, mut context) = create_test_engine(2000);

        // 1. insert account to storage
        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        storage_engine
            .set_values(
                &mut context,
                vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        // 2. delete account in overlay
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(path.clone().into(), None);
        let overlay = overlay_mut.freeze();

        // 3. compute should return None
        let proof = storage_engine
            .compute_account_with_proof_with_overlay(&context, path.clone(), overlay)
            .unwrap();
        assert!(proof.is_none());
    }

    #[test]
    fn test_compute_account_from_overlay_partial_update() {
        let (storage_engine, mut context) = create_test_engine(2000);
        
        let address1 = address!("0x0000000000000000000000000000000000000001");
        let path1 = AddressPath::for_address(address1);
        let account1 = create_test_account(1, 1);
        
        // Another account to force branch structure later if needed, but let's stick to 1 for simplicity first
        // actually let's add a second account to DB so we have a branch
        let address2 = address!("0x0000000000000000000000000000000000000002");
        let path2 = AddressPath::for_address(address2);
        let account2 = create_test_account(2, 2);

        storage_engine
            .set_values(
                &mut context,
                vec![
                    (path1.clone().into(), Some(account1.clone().into())),
                    (path2.clone().into(), Some(account2.clone().into()))
                ].as_mut(),
            )
            .unwrap();

        // Update Account 1 in overlay
        let mut overlay_mut = OverlayStateMut::new();
        let new_account1 = Account::new(10, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        overlay_mut.insert(path1.clone().into(), Some(OverlayValue::Account(new_account1.clone())));
        let overlay = overlay_mut.freeze();

        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        // Get proof for Account 1 (overlayed)
        let proof1 = storage_engine.compute_account_with_proof_with_overlay(&context, path1.clone(), overlay.clone()).unwrap().unwrap();
        assert_eq!(proof1.account, new_account1);
        verify_account_proof(&proof1, overlay_root);

        // Get proof for Account 2 (not overlayed, but proof path affected by root change if any)
        // Note: compute_account_with_proof_with_overlay should work for non-overlayed accounts too if they are in the trie 
        // derived from DB + overlay.
        
        // Wait, compute_account_with_proof_with_overlay logic builds the overlay trie. 
        // If account 2 is stored in DB, it will be included in the trie build process.
        let proof2 = storage_engine.compute_account_with_proof_with_overlay(&context, path2.clone(), overlay).unwrap().unwrap();
        assert_eq!(proof2.account, account2);
        verify_account_proof(&proof2, overlay_root);
    }

    #[test]
    fn test_compute_account_from_overlay_branch_creation() {
        let (storage_engine, mut context) = create_test_engine(2000);
        
        // Construct paths explicitly to force branching
        // Path A: 0x1000... (starts with nibble 1, then 0)
        let mut bytes_a = [0u8; 32]; 
        bytes_a[0] = 0x10; 
        let path_a = AddressPath::new(Nibbles::unpack(B256::from(bytes_a)));
        
        // Path B: 0x1100... (starts with nibble 1, then 1)
        let mut bytes_b = [0u8; 32]; 
        bytes_b[0] = 0x11;
        let path_b = AddressPath::new(Nibbles::unpack(B256::from(bytes_b)));

        let account_a = create_test_account(1, 1);
        let account_b = create_test_account(2, 2);

        // 1. Put Account A in DB
        storage_engine.set_values(
                &mut context,
                vec![(path_a.clone().into(), Some(account_a.clone().into()))].as_mut(),
            ).unwrap();

        // 2. Put Account B in Overlay
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(path_b.clone().into(), Some(OverlayValue::Account(account_b.clone())));
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let root = output.root;

        // 3. Verify proofs for both
        let proof_a = storage_engine.compute_account_with_proof_with_overlay(&context, path_a.clone(), overlay.clone()).unwrap().unwrap();
        verify_account_proof(&proof_a, root);
        assert_eq!(proof_a.account, account_a);

        let proof_b = storage_engine.compute_account_with_proof_with_overlay(&context, path_b.clone(), overlay).unwrap().unwrap();
        verify_account_proof(&proof_b, root);
        assert_eq!(proof_b.account, account_b);
    }

    #[test]
    fn test_compute_storage_from_overlay() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        let slot_key = B256::from(U256::from(99));
        let storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), slot_key.into());
        let storage_value = U256::from(8888);

        // 1. Setup DB with account
        storage_engine
            .set_values(
                &mut context,
                vec![(account_path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        // 2. Overlay adds storage
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage_path.clone().into(), Some(OverlayValue::Storage(storage_value)));
        
        let overlay = overlay_mut.freeze();
        
        // Compute root
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;
        
        // Compute proof
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path.clone(), 
            overlay
        ).unwrap().unwrap();
        
        verify_account_proof(&proof, overlay_root);

        assert!(!proof.storage_proofs.is_empty());
        let sp_key = B256::from_slice(&RawPath::from(storage_path.get_slot().clone()).pack::<32>());
        let sp = proof.storage_proofs.get(&sp_key)
            .expect("storage proof not found");
        assert_eq!(sp.value, storage_value);
    }
    
    #[test]
    fn test_compute_storage_db_updated_in_overlay() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        let slot_key = B256::from(U256::from(10));
        let storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), slot_key.into());
        let db_value = U256::from(1111);
        let overlay_value = U256::from(2222);

        // 1. Setup DB with account and storage
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path.clone().into(), Some(db_value.into()))
                ].as_mut(),
            )
            .unwrap();

        // 2. Overlay updates storage
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage_path.clone().into(), Some(OverlayValue::Storage(overlay_value)));
        
        let overlay = overlay_mut.freeze();
        
        // Compute root
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;
        
        // Compute proof
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path.clone(), 
            overlay
        ).unwrap().unwrap();
        
        verify_account_proof(&proof, overlay_root);
        
        let sp_key = B256::from_slice(&RawPath::from(storage_path.get_slot().clone()).pack::<32>());
        let sp = proof.storage_proofs.get(&sp_key).unwrap();
        assert_eq!(sp.value, overlay_value);
    }

    #[test]
    fn test_compute_storage_in_db_not_overlay() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        let slot_key = B256::from(U256::from(10));
        let storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), slot_key.into());
        let db_value = U256::from(1111);

        // 1. Setup DB with account and storage
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path.clone().into(), Some(db_value.into()))
                ].as_mut(),
            )
            .unwrap();

        // 2. Overlay has changes to OTHER slot
        let other_slot_key = B256::from(U256::from(20));
        let other_storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), other_slot_key.into());
        let other_value = U256::from(9999);

        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(other_storage_path.into(), Some(OverlayValue::Storage(other_value)));
        
        let overlay = overlay_mut.freeze();
        
        // Compute root
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;
        
        // Compute proof for the DB-only slot
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path.clone(), 
            overlay
        ).unwrap().unwrap();
        
        verify_account_proof(&proof, overlay_root);
        
        let sp_key = B256::from_slice(&RawPath::from(storage_path.get_slot().clone()).pack::<32>());
        let sp = proof.storage_proofs.get(&sp_key).unwrap();
        assert_eq!(sp.value, db_value);
    }
    
    #[test]
    fn test_compute_storage_deleted_in_overlay() {
         let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        let slot_key = B256::from(U256::from(10));
        let storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), slot_key.into());
        let db_value = U256::from(1111);

        // 1. Setup DB with account and storage
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path.clone().into(), Some(db_value.into()))
                ].as_mut(),
            )
            .unwrap();

        // 2. Overlay deletes the slot (sets to 0)
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage_path.clone().into(), Some(OverlayValue::Storage(U256::ZERO)));
        
        let overlay = overlay_mut.freeze();
         
        // Compute root
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        // Compute proof
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path.clone(), 
            overlay
        ).unwrap().unwrap();
        
        verify_account_proof(&proof, overlay_root);

        assert!(!proof.storage_proofs.is_empty());
        let sp_key = B256::from_slice(&RawPath::from(storage_path.get_slot().clone()).pack::<32>());
        let sp = proof.storage_proofs.get(&sp_key)
            .expect("storage proof not found");
        assert_eq!(sp.value, U256::ZERO);
    }

    #[test]
    fn test_compute_storage_non_existent_account() {
        let (storage_engine, context) = create_test_engine(2000);
        let overlay_mut = OverlayStateMut::new();
        let overlay = overlay_mut.freeze();
        
        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let slot_key = B256::from(U256::from(10));
        let storage_path = StoragePath::for_address_path_and_slot(account_path, slot_key.into());

        // Account doesn't exist in DB or Overlay
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path, 
            overlay
        ).unwrap();
        
        assert!(proof.is_none());
    }

    #[test]
    fn test_compute_storage_non_existent_slot() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        // 1. Setup DB with account ONLY (no storage)
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                ].as_mut(),
            )
            .unwrap();

        // 2. Empty Overlay
        let overlay_mut = OverlayStateMut::new();
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        // 3. Request proof for random slot
        let slot_key = B256::from(U256::from(555));
        let storage_path = StoragePath::for_address_path_and_slot(account_path, slot_key.into());

        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path.clone(), 
            overlay
        ).unwrap().unwrap();
        
        // Should find account
        verify_account_proof(&proof, overlay_root);
        
        // Storage proof should exist giving value 0 (Exclusion Proof)
        assert!(!proof.storage_proofs.is_empty());
        let sp_key = B256::from_slice(&RawPath::from(storage_path.get_slot().clone()).pack::<32>());
        let sp = proof.storage_proofs.get(&sp_key)
            .expect("storage proof not found");
        assert_eq!(sp.value, U256::ZERO);
    }

    #[test]
    fn test_compute_storage_branch_creation() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        // Slot A: Starts with 0x01...
        let mut slot_a_bytes = [0u8; 32]; slot_a_bytes[0] = 0x10;
        let slot_a = B256::from(slot_a_bytes);
        let storage_path_a = StoragePath::for_address_path_and_slot(account_path.clone(), slot_a.into());
        let val_a = U256::from(100);

        // Slot B: Starts with 0x02... (Forces branch at first nibble if they share prefix, or just specific structure)
        // Let's use 0x11... to share first nibble '1' but differ at second '1'.
        let mut slot_b_bytes = [0u8; 32]; slot_b_bytes[0] = 0x11;
        let slot_b = B256::from(slot_b_bytes);
        let storage_path_b = StoragePath::for_address_path_and_slot(account_path.clone(), slot_b.into());
        let val_b = U256::from(200);

        // 1. Setup DB with Account and Slot A
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path_a.clone().into(), Some(val_a.into())),
                ].as_mut(),
            )
            .unwrap();

        // 2. Overlay adds Slot B (Creating a branch node where previously there might have been leaf/extension)
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage_path_b.clone().into(), Some(OverlayValue::Storage(val_b)));
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        // 3. Verify Proof for Slot A (from DB, now under branch)
        let proof_a = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path_a.clone(), 
            overlay.clone()
        ).unwrap().unwrap();
        
        verify_account_proof(&proof_a, overlay_root);
        let sp_key_a = B256::from_slice(&RawPath::from(storage_path_a.get_slot().clone()).pack::<32>());
        assert_eq!(proof_a.storage_proofs.get(&sp_key_a).unwrap().value, val_a);

        // 4. Verify Proof for Slot B (from Overlay)
        let proof_b = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path_b.clone(), 
            overlay
        ).unwrap().unwrap();
        
        verify_account_proof(&proof_b, overlay_root);
        let sp_key_b = B256::from_slice(&RawPath::from(storage_path_b.get_slot().clone()).pack::<32>());
        assert_eq!(proof_b.storage_proofs.get(&sp_key_b).unwrap().value, val_b);
    }

    #[test]
    fn test_compute_storage_with_tombstoned_account() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        let slot_key = B256::from(U256::from(10));
        let storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), slot_key.into());
        let db_value = U256::from(1111);

        // 1. Setup DB with account and storage
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path.clone().into(), Some(db_value.into()))
                ].as_mut(),
            )
            .unwrap();

        // 2. Overlay DELETEs the entire account
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(account_path.into(), None);
        let overlay = overlay_mut.freeze();
        
        // 3. Request proof for the storage slot
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path, 
            overlay
        ).unwrap();
        
        // Should be None because the account is gone
        assert!(proof.is_none());
    }

    #[test]
    fn test_compute_storage_and_account_modified() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        // Original Account: Nonce 1
        let account = create_test_account(1, 1);
        
        let slot_key = B256::from(U256::from(10));
        let storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), slot_key.into());
        // Original Storage: 1111
        let db_value = U256::from(1111);

        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path.clone().into(), Some(db_value.into()))
                ].as_mut(),
            )
            .unwrap();

        // 2. Overlay updates BOTH Account (Nonce -> 2) and Storage (1111 -> 2222)
        let mut overlay_mut = OverlayStateMut::new();
        
        // Construct new account manually to ensure formatting
        let new_account = Account::new(2, U256::from(1), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        // Warning: In a real Scenario, the storage_root in this OverlayValue::Account is usually ignored 
        // or re-calculated by the state root computation, but we pass it as placeholder.
        overlay_mut.insert(account_path.clone().into(), Some(OverlayValue::Account(new_account.clone())));
        
        let overlay_value = U256::from(2222);
        overlay_mut.insert(storage_path.clone().into(), Some(OverlayValue::Storage(overlay_value)));
        
        let overlay = overlay_mut.freeze();
        
        // Compute state root to establish the ground truth
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        // 3. Request Proof
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path.clone(), 
            overlay
        ).unwrap().unwrap();

        // 4. Verify
        verify_account_proof(&proof, overlay_root);
        
        // Check Account Nonce updated
        assert_eq!(proof.account.nonce, 2);
        
        // Check Storage Value updated
        let sp_key = B256::from_slice(&RawPath::from(storage_path.get_slot().clone()).pack::<32>());
        assert_eq!(proof.storage_proofs.get(&sp_key).unwrap().value, overlay_value);
    }
    
    #[test]
    fn test_compute_storage_collapsing_branch() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        // Setup two slots creating a branch in DB
        // Slot A: 0x10...
        let mut slot_a_bytes = [0u8; 32]; slot_a_bytes[0] = 0x10;
        let slot_a = B256::from(slot_a_bytes);
        let storage_path_a = StoragePath::for_address_path_and_slot(account_path.clone(), slot_a.into());
        let val_a = U256::from(100);

        // Slot B: 0x11...
        let mut slot_b_bytes = [0u8; 32]; slot_b_bytes[0] = 0x11;
        let slot_b = B256::from(slot_b_bytes);
        let storage_path_b = StoragePath::for_address_path_and_slot(account_path.clone(), slot_b.into());
        let val_b = U256::from(200);

        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path_a.clone().into(), Some(val_a.into())),
                    (storage_path_b.clone().into(), Some(val_b.into())),
                ].as_mut(),
            )
            .unwrap();

        // 2. Overlay DELETES Slot B
        // This should cause the trie node for Slot A to effectively merge/simplify if optimizing
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(storage_path_b.clone().into(), Some(OverlayValue::Storage(U256::ZERO)));
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;

        // 3. Request Proof for Slot A
        let proof_a = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path_a.clone(), 
            overlay
        ).unwrap().unwrap();
        
        verify_account_proof(&proof_a, overlay_root);
        let sp_key_a = B256::from_slice(&RawPath::from(storage_path_a.get_slot().clone()).pack::<32>());
        assert_eq!(proof_a.storage_proofs.get(&sp_key_a).unwrap().value, val_a);
    }

    #[test]
    fn test_compute_storage_exclusion_with_neighbor() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        
        // Slot A (Exists in DB): 0x10...
        let mut slot_a_bytes = [0u8; 32]; slot_a_bytes[0] = 0x10;
        let slot_a = B256::from(slot_a_bytes);
        let storage_path_a = StoragePath::for_address_path_and_slot(account_path.clone(), slot_a.into());
        let val_a = U256::from(100);

        // Slot B (Missing): 0x11... (Shares prefix '1' with A, differs at second nibble)
        let mut slot_b_bytes = [0u8; 32]; slot_b_bytes[0] = 0x11;
        let slot_b = B256::from(slot_b_bytes);
        let storage_path_b = StoragePath::for_address_path_and_slot(account_path.clone(), slot_b.into());

        // 1. Setup DB with Slot A
        storage_engine
            .set_values(
                &mut context,
                vec![
                    (account_path.clone().into(), Some(account.clone().into())),
                    (storage_path_a.clone().into(), Some(val_a.into())),
                ].as_mut(),
            )
            .unwrap();
            
        // 2. Empty Overlay
        let overlay_mut = OverlayStateMut::new();
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;
        
        // 3. Request Proof for MISSING Slot B
        // This should return an inclusion proof for the branch node + exclusion for the leaf
        let proof_b = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path_b.clone(), 
            overlay
        ).unwrap().unwrap();
        
        // Verify Account Proof
        verify_account_proof(&proof_b, overlay_root);
        
        // Verify Storage Exclusion Proof
        assert!(!proof_b.storage_proofs.is_empty());
        let sp_key_b = B256::from_slice(&RawPath::from(storage_path_b.get_slot().clone()).pack::<32>());
        let sp = proof_b.storage_proofs.get(&sp_key_b).unwrap();
        
        assert_eq!(sp.value, U256::ZERO);
        // The proof should likely contain the branch node common to A and B
        assert!(sp.proof.len() >= 1);
    }

    #[test]
    fn test_compute_storage_from_new_account_in_overlay() {
        let (storage_engine, context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let account_path = AddressPath::for_address(address);
        // New Account
        let account = create_test_account(1, 1);
        
        let slot_key = B256::from(U256::from(10));
        let storage_path = StoragePath::for_address_path_and_slot(account_path.clone(), slot_key.into());
        let val = U256::from(12345);

        // 1. Storage is EMPTY
        
        // 2. Overlay creates Account AND Storage
        let mut overlay_mut = OverlayStateMut::new();
        overlay_mut.insert(account_path.clone().into(), Some(OverlayValue::Account(account.clone())));
        overlay_mut.insert(storage_path.clone().into(), Some(OverlayValue::Storage(val)));
        
        let overlay = overlay_mut.freeze();
        
        let output = storage_engine.compute_state_root_with_overlay(&context, overlay.clone()).unwrap();
        let overlay_root = output.root;
        
        // 3. Request Proof for Storage
        let proof = storage_engine.compute_storage_with_proof_with_overlay(
            &context, 
            storage_path.clone(), 
            overlay
        ).unwrap().unwrap();
        
        verify_account_proof(&proof, overlay_root);
        
        let sp_key = B256::from_slice(&RawPath::from(storage_path.get_slot().clone()).pack::<32>());
        assert_eq!(proof.storage_proofs.get(&sp_key).unwrap().value, val);
        
        // Also verify account matches (it should have the computed storage root, not empty)
        assert_ne!(proof.account.storage_root, EMPTY_ROOT_HASH);
        assert_eq!(proof.account.nonce, account.nonce);
        assert_eq!(proof.account.balance, account.balance);
    }
}