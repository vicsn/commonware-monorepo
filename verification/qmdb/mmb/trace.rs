//! Run the pinned Tempo dependency's OperationProof::verify with a SHA-256 call trace.
//! Each printed path follows the argument boundaries of actual, successful verifier calls.

use commonware_cryptography::{Hasher, Sha256, sha256::Digest};
use commonware_storage::{
    merkle::{Proof, mmb},
    qmdb::current::proof::{OperationProof, RangeProof},
};
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
};

#[derive(Default)]
struct Trace(Sha256);

thread_local! {
    static INPUTS: RefCell<HashMap<Vec<u8>, Vec<Vec<u8>>>> = RefCell::default();
}

impl Hasher for Trace {
    type Digest = Digest;

    fn hash(parts: &[&[u8]]) -> Digest {
        let digest = Sha256::hash(parts);
        INPUTS.with_borrow_mut(|inputs| {
            inputs.insert(
                digest.as_ref().to_vec(),
                parts.iter().map(|p| p.to_vec()).collect(),
            );
        });
        digest
    }

    fn hash_pair(left: &[&[u8]], right: &[&[u8]]) -> (Digest, Digest) {
        (Self::hash(left), Self::hash(right))
    }

    fn update(&mut self, part: &[u8]) -> &mut Self {
        self.0.update(part);
        self
    }

    fn finalize(self) -> (Self, Digest) {
        let (fresh, digest) = self.0.finalize();
        (Self(fresh), digest)
    }
}

// Follow a hash into its right-associated concatenation of arguments.
fn path(root: &[u8], tip: &[u8]) -> Option<String> {
    if root == tip {
        return Some(String::new());
    }
    INPUTS.with_borrow(|inputs| {
        let parts = inputs.get(root)?;
        parts.iter().enumerate().find_map(|(i, part)| {
            let suffix = path(part, tip)?;
            let last = if i + 1 == parts.len() { "" } else { "L" };
            Some(format!("H{}{last}{suffix}", "R".repeat(i)))
        })
    })
}

// Render the complete preimage tree, keeping digests supplied by the peer opaque.
fn transcript(term: &[u8]) -> String {
    INPUTS.with_borrow(|inputs| {
        if let Some(parts) = inputs.get(term) {
            let mut iter = parts.iter().rev().map(|p| transcript(p));
            let last = iter.next().expect("nonempty hash input");
            let body = iter.fold(last, |right, left| format!("({left},{right})"));
            format!("H{body}")
        } else {
            term.iter().map(|b| format!("{b:02x}")).collect()
        }
    })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn sample(leaves: u64, inactive: usize, loc: u64) {
    let ops = Sha256::hash(&[b"ops"]);
    let arbitrary = Sha256::hash(&[b"external digest"]);
    let item = [0x3au8; 32];
    let chunk = [0xbdu8; 32];
    if chunk[(loc % 256 / 8) as usize] & (1 << (loc % 8)) == 0 {
        return;
    }
    let chunk_digest = Sha256::hash(&[&chunk]);
    let complete = leaves / 256;
    let grafted = if leaves < 383 {
        0
    } else {
        (leaves - 383) / 256 + 1
    };
    let trailing = |idx| {
        if loc / 256 == idx {
            chunk_digest
        } else {
            arbitrary
        }
    };
    let mut proof = OperationProof {
        loc: mmb::Location::new(loc),
        chunk,
        range_proof: RangeProof {
            proof: Proof {
                leaves: mmb::Location::new(leaves),
                inactive_peaks: inactive,
                digests: Vec::new(),
            },
            pending_chunk_digest: (grafted < complete).then(|| trailing(grafted)),
            partial_chunk_digest: (leaves % 256 != 0).then(|| trailing(complete)),
            ops_root: ops,
        },
    };

    // Discover the required proof size and root through the production verifier. Opaque
    // sibling values suffice because we are checking the verifier's paths to its inputs.
    for _ in 0..=128 {
        INPUTS.with_borrow_mut(HashMap::clear);
        proof.verify::<Trace, _>(item, &arbitrary);
        let root = INPUTS.with_borrow(|inputs| {
            inputs
                .values()
                .find(|args| args.first().is_some_and(|p| p == ops.as_ref()))
                .map(|parts| {
                    let parts: Vec<_> = parts.iter().map(Vec::as_slice).collect();
                    Sha256::hash(&parts)
                })
        });
        if let Some(root) = root {
            assert!(proof.verify::<Trace, _>(item, &root));
            let op_path = path(root.as_ref(), &item).expect("missing operation in hash trace");
            let chunk_path = path(root.as_ref(), &chunk).expect("missing chunk in hash trace");
            let digests = proof
                .range_proof
                .proof
                .digests
                .iter()
                .map(|d| hex(d.as_ref()))
                .collect::<Vec<_>>()
                .join(",");
            let trace = transcript(root.as_ref());
            println!(
                "{leaves} {inactive} {loc} {op_path} {chunk_path} {} {} {digests} {trace}",
                hex(ops.as_ref()),
                hex(arbitrary.as_ref())
            );
            assert!(!proof.verify::<Trace, _>([0x3bu8; 32], &root));
            assert!(!proof.verify::<Trace, _>(item, &arbitrary));
            proof.range_proof.proof.digests.push(arbitrary);
            assert!(!proof.verify::<Trace, _>(item, &root));
            proof.range_proof.proof.digests.pop();
            if let Some(last) = proof.range_proof.proof.digests.pop() {
                assert!(!proof.verify::<Trace, _>(item, &root));
                proof.range_proof.proof.digests.push(last);
            }
            proof.range_proof.partial_chunk_digest = match proof.range_proof.partial_chunk_digest {
                Some(_) => None,
                None => Some(arbitrary),
            };
            assert!(!proof.verify::<Trace, _>(item, &root));
            proof.range_proof.partial_chunk_digest =
                (leaves % 256 != 0).then(|| trailing(complete));
            proof.chunk = [0; 32];
            assert!(!proof.verify::<Trace, _>(item, &root));
            return;
        }
        let i = proof.range_proof.proof.digests.len() as u64;
        proof
            .range_proof
            .proof
            .digests
            .push(Sha256::hash(&[b"sibling", &i.to_be_bytes()]));
    }
    panic!("no accepted proof for leaves={leaves} inactive={inactive} loc={loc}");
}

fn main() {
    for leaves in [
        1, 2, 5, 11, 127, 255, 256, 257, 382, 383, 384, 511, 512, 639, 777,
    ] {
        for inactive in 0..=(leaves + 1u64).ilog2() as usize {
            for loc in [
                0,
                2,
                7,
                31,
                64,
                126,
                128,
                254,
                255,
                256,
                382,
                383,
                508,
                512,
                leaves - 1,
            ]
            .into_iter()
            .collect::<BTreeSet<_>>()
            {
                if loc < leaves {
                    sample(leaves, inactive, loc);
                }
            }
        }
    }
}
