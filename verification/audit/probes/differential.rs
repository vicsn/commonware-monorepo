// Differential probes of the audit. They vary what `qmdb/tests.rs` never varies: the bagging
// policy, tree sizes that are not a power of two, the proof's own fields and the height that the
// client trusts. The last one shows a fact about bytes that the ideal hash cannot express. They
// print counts and assert nothing. Run them from the repository root:
//
//     cat verification/audit/probes/differential.rs >> verification/symbolic/src/qmdb/tests.rs
//     (cd verification/symbolic && cargo test --offline -- --nocapture probe)
//     git checkout verification/symbolic/src/qmdb/tests.rs

fn build(hasher: &Production, items: &[Vec<u8>]) -> Mmr<sha256::Digest> {
    let mut mmr = Mmr::new();
    let batch = {
        let mut batch = mmr.new_batch();
        for item in items {
            batch = batch.add(hasher, item);
        }
        batch.merkleize(&mmr, hasher)
    };
    mmr.apply_batch(&batch).unwrap();
    mmr
}

/// The hasher that QMDB itself uses for operation roots.
#[test]
fn probe_qmdb_hasher() {
    let hasher: Production = commonware_storage::qmdb::hasher::<Sha256>();
    let mut rng = test_rng();
    let (mut honest, mut production, mut client) = (0, 0, 0);
    for height in 0..=6u32 {
        let leaves = 1u64 << height;
        let items = random_items(&mut rng, leaves);
        let mmr = build(&hasher, &items);
        let root = mmr.root(&hasher, 0).unwrap();
        for location in 0..leaves {
            let proof = mmr.proof(&hasher, Location::new(location), 0).unwrap();
            let item = &items[location as usize];
            honest += 1;
            if proof.verify_element_inclusion(&hasher, Location::new(location), item, &root) {
                production += 1;
            }
            let siblings: Vec<_> = proof.digests.iter().map(bytes).collect();
            if qmdb::verify(&Concrete, height, location, &bytes(&root), item, &siblings) {
                client += 1;
            }
        }
    }
    println!(
        "PROBE qmdb hasher: {honest} honest openings, production accepts {production}, \
         client accepts {client}"
    );
}

/// Tree sizes that are not a power of two, with the forward-fold hasher of the tests.
#[test]
fn probe_other_sizes() {
    let hasher = Production::new(Bagging::ForwardFold);
    let mut rng = test_rng();
    let (mut honest, mut production, mut client) = (0, 0, 0);
    for leaves in 1..=64u64 {
        if leaves.is_power_of_two() {
            continue;
        }
        let items = random_items(&mut rng, leaves);
        let mmr = build(&hasher, &items);
        let root = mmr.root(&hasher, 0).unwrap();
        for location in 0..leaves {
            let proof = mmr.proof(&hasher, Location::new(location), 0).unwrap();
            let item = &items[location as usize];
            honest += 1;
            if proof.verify_element_inclusion(&hasher, Location::new(location), item, &root) {
                production += 1;
            }
            let siblings: Vec<_> = proof.digests.iter().map(bytes).collect();
            for height in 0..=7u32 {
                if qmdb::verify(&Concrete, height, location, &bytes(&root), item, &siblings) {
                    client += 1;
                }
            }
        }
    }
    println!(
        "PROBE other sizes: {honest} honest openings, production accepts {production}, \
         client accepts {client} at any height from 0 to 7"
    );
}

/// The proof fields that the attacker writes and the differential tests never vary.
#[test]
fn probe_proof_fields() {
    let hasher = Production::new(Bagging::ForwardFold);
    let mut rng = test_rng();
    let (mut altered, mut accepted) = (0u64, 0u64);
    for height in 0..=6u32 {
        let leaves = 1u64 << height;
        let items = random_items(&mut rng, leaves);
        let mmr = build(&hasher, &items);
        let root = mmr.root(&hasher, 0).unwrap();
        for location in 0..leaves {
            let proof = mmr.proof(&hasher, Location::new(location), 0).unwrap();
            let item = &items[location as usize];
            for claimed in 0..=2 * leaves + 2 {
                for inactive in 0..=3usize {
                    if claimed == leaves && inactive == 0 {
                        continue;
                    }
                    let claim = Proof {
                        leaves: Location::new(claimed),
                        inactive_peaks: inactive,
                        digests: proof.digests.clone(),
                    };
                    altered += 1;
                    if claim.verify_element_inclusion(&hasher, Location::new(location), item, &root)
                    {
                        accepted += 1;
                    }
                }
            }
        }
    }
    println!(
        "PROBE proof fields: {altered} proofs with another size or inactive peak count, \
         production accepts {accepted}"
    );
}

/// A client that trusts another height than the tree's.
#[test]
fn probe_wrong_height() {
    let hasher = Production::new(Bagging::ForwardFold);
    let mut rng = test_rng();
    let (mut tried, mut accepted) = (0u64, 0u64);
    for height in 0..=6u32 {
        let leaves = 1u64 << height;
        let items = random_items(&mut rng, leaves);
        let mmr = build(&hasher, &items);
        let root = bytes(&mmr.root(&hasher, 0).unwrap());
        for location in 0..leaves {
            let proof = mmr.proof(&hasher, Location::new(location), 0).unwrap();
            let item = &items[location as usize];
            let siblings: Vec<_> = proof.digests.iter().map(bytes).collect();
            for trusted in 0..=10u32 {
                if trusted == height {
                    continue;
                }
                tried += 1;
                if qmdb::verify(&Concrete, trusted, location, &root, item, &siblings) {
                    accepted += 1;
                }
            }
        }
    }
    println!("PROBE wrong height: {tried} honest openings at another height, client accepts {accepted}");
}

/// What the ideal hash cannot express: in bytes, the root input of a small forward-fold tree is
/// also the leaf input at position 0 of a 34-byte item.
#[test]
fn probe_root_is_a_leaf_input() {
    use commonware_storage::merkle::{hasher::Hasher as _, mmr::Position};
    let hasher = Production::new(Bagging::ForwardFold);
    let mut rng = test_rng();
    let (mut trees, mut same) = (0, 0);
    for height in 0..=6u32 {
        let leaves = 1u64 << height;
        let items = random_items(&mut rng, leaves);
        let mmr = build(&hasher, &items);
        let root = mmr.root(&hasher, 0).unwrap();
        // The peak of a tree with one peak is its last node.
        let peak = mmr.get_node(Position::new(2 * leaves - 2)).unwrap();
        let mut item = leaves.to_be_bytes()[6..].to_vec();
        item.extend_from_slice(peak.as_ref());
        trees += 1;
        if hasher.leaf_digest(Position::new(0), &item) == root {
            same += 1;
        }
    }
    println!(
        "PROBE root as leaf input: {same} of {trees} roots equal the leaf digest at position 0 \
         of a 34-byte item"
    );
}
