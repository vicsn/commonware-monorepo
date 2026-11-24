//! Differential tests of the reads client against production: current ordered databases over an
//! MMB with 32-byte keys and values, whose key-value and exclusion proofs production's
//! `KeyValueProof::verify` and `ExclusionProof::verify` check. The databases are built at once or
//! through a history of updates and deletes, which yields proofs with pending and partial chunks
//! and inactive peaks. On every honest proof, on altered claims (another value, another
//! successor, another root, another key) and on proofs with one field altered, the client must
//! return production's verdict. Every honest proof must be accepted and every altered proof
//! rejected.

use super::{
    Digest, ExclusionProof, Key, OperationProof, Payload, Proof, Update, ValueEncoding,
    verify_exclusion, verify_member,
};
use crate::{
    concrete::{Concrete, bytes},
    layout::{self, Widths, Writer},
};
use commonware_cryptography::{Sha256, sha256};
use commonware_parallel::Sequential;
use commonware_runtime::{Runner as _, Supervisor as _, buffer::paged::CacheRef, deterministic};
use commonware_storage::{
    journal::{authenticated::Config as MerkleConfig, contiguous::fixed::Config as LogConfig},
    merkle::mmb,
    qmdb::{
        current::{
            ordered::{
                self as production,
                fixed::{Config, Db},
            },
            proof::operation::Proof as ProductionProof,
        },
        value::FixedEncoding,
    },
    translator::TwoCap,
};
use commonware_utils::{NZU16, NZU64, NZUsize, sequence::FixedBytes, test_rng};
use rand::RngExt as _;
use std::collections::BTreeMap;

type Key32 = FixedBytes<32>;
type Value32 = FixedBytes<32>;
type Database =
    Db<mmb::Family, deterministic::Context, Key32, Value32, Sha256, TwoCap, 32, Sequential>;
type Operation = ProductionProof<mmb::Family, sha256::Digest, [u8; 32]>;

impl Key for Key32 {
    fn less(&self, other: &Self) -> bool {
        self < other
    }
}

impl Digest for [u8; 32] {}

/// The fixed encoding of 32-byte values.
struct Fixed;

impl ValueEncoding for Fixed {
    type Value = Value32;
}

/// A buffer that production's fixed codec of 32-byte keys and values writes into.
#[derive(Default)]
struct Buffer(Vec<u8>);

impl Writer for Buffer {
    type Key = Key32;
    type Value = Value32;
    type Update = Update<Key32, Fixed>;

    fn byte(&mut self, byte: u8) {
        self.0.push(byte);
    }

    fn zeros(&mut self, count: usize) {
        self.0.resize(self.0.len() + count, 0);
    }

    fn word(&mut self, word: u64) {
        self.0.extend_from_slice(&word.to_be_bytes());
    }

    fn key(&mut self, key: &Key32) {
        self.0.extend_from_slice(key.as_ref());
    }

    fn value(&mut self, value: &Value32) {
        self.0.extend_from_slice(value.as_ref());
    }

    fn update(&mut self, update: &Self::Update) {
        layout::write_ordered_update(self, &update.key, &update.value, &update.next_key);
    }
}

impl AsRef<[u8]> for Buffer {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

const WIDTHS: Widths = Widths {
    key: 32,
    value: 32,
    update: 96,
};

/// The fields of a production operation proof, owned so that the client's proof can borrow them.
struct Fields {
    loc: u64,
    ops_root: [u8; 32],
    leaves: u64,
    inactive: usize,
    digests: Vec<[u8; 32]>,
    pending: Option<[u8; 32]>,
    partial: Option<[u8; 32]>,
    chunk: [u8; 32],
}

impl Fields {
    fn of(proof: &Operation) -> Self {
        let range = &proof.range_proof;
        Self {
            loc: *proof.loc,
            ops_root: bytes(&range.ops_root),
            leaves: *range.proof.leaves,
            inactive: range.proof.inactive_peaks,
            digests: range.proof.digests.iter().map(bytes).collect(),
            pending: range.pending_chunk_digest.as_ref().map(bytes),
            partial: range.partial_chunk_digest.as_ref().map(bytes),
            chunk: proof.chunk,
        }
    }

    fn proof(&self) -> Proof<'_, [u8; 32]> {
        OperationProof {
            loc: self.loc,
            payload: (
                self.ops_root,
                Payload {
                    leaves: self.leaves,
                    inactive: self.inactive,
                    digests: &self.digests,
                    pending: self.pending,
                    partial: self.partial,
                    chunk: &self.chunk,
                },
            ),
        }
    }
}

fn key(seed: u64) -> Key32 {
    let mut raw = [0u8; 32];
    raw[..8].copy_from_slice(&seed.to_be_bytes());
    Key32::new(raw)
}

fn value(seed: u64) -> Value32 {
    let mut raw = [0u8; 32];
    raw[24..].copy_from_slice(&seed.to_be_bytes());
    Value32::new(raw)
}

fn other_root(root: &sha256::Digest) -> sha256::Digest {
    let mut raw = bytes(root);
    raw[0] ^= 1;
    sha256::Digest::from(raw)
}

async fn open(context: deterministic::Context, name: &str) -> Database {
    let cfg = Config {
        merkle: MerkleConfig {
            partition: format!("reads-{name}-merkle"),
            replay_buffer: NZUsize!(1024),
            strategy: Sequential,
            resident_height: Default::default(),
        },
        log: LogConfig {
            partition: format!("reads-{name}-log"),
            items_per_blob: NZU64!(7),
            write_buffer: NZUsize!(1024),
            replay_buffer: NZUsize!(1024),
            page_cache: CacheRef::new(NZU16!(91), NZUsize!(8)),
        },
        grafted_metadata_partition: format!("reads-{name}-grafted"),
        translator: TwoCap,
        init_cache: Some(NZUsize!(3)),
        init_buffer: NZUsize!(1 << 16),
        init_concurrency: NZUsize!(1),
    };
    Database::init(context, cfg, None).await.unwrap()
}

async fn apply(db: Database, writes: Vec<(Key32, Option<Value32>)>) -> Database {
    let mut batch = db.new_batch();
    for (k, v) in writes {
        batch = batch.write(k, v);
    }
    let merkleized = batch.merkleize(&db).await.unwrap();
    let db = db.apply_batch(merkleized).await.unwrap();
    db.commit().await.unwrap()
}

fn member(
    proof: &production::proof::constant::KeyValueProof<mmb::Family, Key32, sha256::Digest, 32>,
    k: &Key32,
    v: &Value32,
    next: &Key32,
    root: &sha256::Digest,
) -> (bool, bool) {
    let altered = production::proof::constant::KeyValueProof {
        proof: proof.proof.clone(),
        next_key: next.clone(),
    };
    let expected = altered.verify::<Sha256, FixedEncoding<Value32>>(k.clone(), v.clone(), root);
    let fields = Fields::of(&proof.proof);
    let actual = verify_member::<Key32, Fixed, Concrete, Buffer>(
        &Concrete,
        &WIDTHS,
        Buffer::default(),
        k.clone(),
        v.clone(),
        next,
        &fields.proof(),
        &bytes(root),
    );
    (expected, actual)
}

fn exclusion(
    proof: &production::proof::constant::ExclusionProof<
        mmb::Family,
        Key32,
        FixedEncoding<Value32>,
        sha256::Digest,
        32,
    >,
    k: &Key32,
    root: &sha256::Digest,
) -> (bool, bool) {
    let expected = proof.verify::<Sha256>(k, root);
    let (operation, stand_in) = match proof {
        production::proof::ExclusionProof::KeyValue(operation, update) => (
            operation,
            Some(Update::<Key32, Fixed> {
                key: update.key.clone(),
                value: update.value.clone(),
                next_key: update.next_key.clone(),
            }),
        ),
        production::proof::ExclusionProof::Commit(operation, _) => (operation, None),
    };
    let fields = Fields::of(operation);
    let client = match (proof, stand_in) {
        (_, Some(update)) => ExclusionProof::KeyValue(fields.proof(), update),
        (production::proof::ExclusionProof::Commit(_, metadata), None) => {
            ExclusionProof::Commit(fields.proof(), metadata.clone())
        }
        _ => unreachable!(),
    };
    let actual = verify_exclusion::<Key32, Fixed, Concrete, Buffer>(
        &Concrete,
        &WIDTHS,
        Buffer::default(),
        k,
        &client,
        &bytes(root),
    );
    (expected, actual)
}

/// Every proof with one field altered: the location, the ops root, the leaf and inactive-peak
/// counts, each range-proof digest, the pending and partial chunk digests, and the chunk.
fn tamperings(proof: &Operation) -> Vec<(String, Operation)> {
    let mut out = Vec::new();
    let mut push = |name: String, f: &dyn Fn(&mut Operation)| {
        let mut altered = proof.clone();
        f(&mut altered);
        out.push((name, altered));
    };
    let loc = *proof.loc;
    for (name, to) in [
        ("loc+1", loc + 1),
        ("loc-1", loc.wrapping_sub(1)),
        ("loc+256", loc + 256),
    ] {
        if to != loc && to < 1 << 40 {
            push(name.into(), &|p| p.loc = mmb::Location::new(to));
        }
    }
    push("ops root".into(), &|p| {
        p.range_proof.ops_root = other_root(&p.range_proof.ops_root)
    });
    let leaves = *proof.range_proof.proof.leaves;
    for (name, to) in [
        ("leaves+1", leaves + 1),
        ("leaves-1", leaves.wrapping_sub(1)),
        ("leaves*2", leaves * 2),
    ] {
        if to != leaves && to < 1 << 40 {
            push(name.into(), &|p| {
                p.range_proof.proof.leaves = mmb::Location::new(to)
            });
        }
    }
    let inactive = proof.range_proof.proof.inactive_peaks;
    push("inactive+1".into(), &|p| {
        p.range_proof.proof.inactive_peaks = inactive + 1
    });
    if inactive > 0 {
        push("inactive-1".into(), &|p| {
            p.range_proof.proof.inactive_peaks = inactive - 1
        });
    }
    let digests = proof.range_proof.proof.digests.len();
    for i in 0..digests {
        push(format!("digest {i}"), &|p| {
            p.range_proof.proof.digests[i] = other_root(&p.range_proof.proof.digests[i])
        });
    }
    if digests > 0 {
        push("digest dropped".into(), &|p| {
            p.range_proof.proof.digests.pop();
        });
    }
    if digests > 1 {
        push("digests swapped".into(), &|p| {
            p.range_proof.proof.digests.swap(0, 1)
        });
    }
    push("digest added".into(), &|p| {
        p.range_proof
            .proof
            .digests
            .push(sha256::Digest::from([7; 32]))
    });
    match proof.range_proof.pending_chunk_digest {
        Some(d) => {
            push("pending altered".into(), &|p| {
                p.range_proof.pending_chunk_digest = Some(other_root(&d))
            });
            push("pending dropped".into(), &|p| {
                p.range_proof.pending_chunk_digest = None
            });
        }
        None => push("pending added".into(), &|p| {
            p.range_proof.pending_chunk_digest = Some(sha256::Digest::from([7; 32]))
        }),
    }
    match proof.range_proof.partial_chunk_digest {
        Some(d) => {
            push("partial altered".into(), &|p| {
                p.range_proof.partial_chunk_digest = Some(other_root(&d))
            });
            push("partial dropped".into(), &|p| {
                p.range_proof.partial_chunk_digest = None
            });
        }
        None => push("partial added".into(), &|p| {
            p.range_proof.partial_chunk_digest = Some(sha256::Digest::from([7; 32]))
        }),
    }
    for bit in 0..256 {
        push(format!("chunk bit {bit}"), &|p| {
            p.chunk[bit / 8] ^= 1 << (bit % 8)
        });
    }
    out
}

/// Counts of the claims checked and of the proof shapes they covered.
#[derive(Default)]
struct Tally {
    claims: usize,
    tampered: usize,
    pending: usize,
    partial: usize,
    inactive: usize,
    commit: usize,
}

impl Tally {
    fn shape(&mut self, proof: &Operation) {
        let range = &proof.range_proof;
        self.pending += range.pending_chunk_digest.is_some() as usize;
        self.partial += range.partial_chunk_digest.is_some() as usize;
        self.inactive += (range.proof.inactive_peaks > 0) as usize;
    }
}

/// Check every live key, and the keys between and beyond them, of `db`, whose live keys are
/// `live` in order. Every `tamper`th proof is also checked with each field altered.
async fn check(db: &Database, live: &[u64], probes: &[u64], tamper: usize, tally: &mut Tally) {
    let root = db.root();
    let wrong = other_root(&root);
    for (i, &seed) in live.iter().enumerate() {
        let k = key(seed);
        let (proof, v) = db.key_value_proof(&k).await.unwrap();
        let next = key(live[(i + 1) % live.len()]);
        assert_eq!(proof.next_key, next);
        tally.shape(&proof.proof);
        let cases = [
            (k.clone(), v.clone(), next.clone(), root, true),
            (
                k.clone(),
                value(seed + 1_000_000),
                next.clone(),
                root,
                false,
            ),
            (k.clone(), v.clone(), key(seed + 1_000_000), root, false),
            (k.clone(), v.clone(), next.clone(), wrong, false),
            (key(seed + 1_000_000), v.clone(), next.clone(), root, false),
        ];
        for (k, v, next, r, honest) in cases {
            let (expected, actual) = member(&proof, &k, &v, &next, &r);
            assert_eq!(expected, honest, "production, key {seed}");
            assert_eq!(actual, expected, "client, key {seed}");
            tally.claims += 1;
        }
        if i % tamper == 0 {
            for (name, altered) in tamperings(&proof.proof) {
                let altered = production::proof::constant::KeyValueProof {
                    proof: altered,
                    next_key: next.clone(),
                };
                let (expected, actual) = member(&altered, &k, &v, &next, &root);
                assert!(!expected, "production, key {seed}, {name}");
                assert_eq!(actual, expected, "client, key {seed}, {name}");
                tally.tampered += 1;
            }
        }
    }
    for (j, &seed) in probes.iter().enumerate() {
        let k = key(seed);
        if live.contains(&seed) {
            continue;
        }
        let proof = db.exclusion_proof(&k).await.unwrap();
        let operation = match &proof {
            production::proof::ExclusionProof::KeyValue(operation, _) => operation,
            production::proof::ExclusionProof::Commit(operation, _) => {
                tally.commit += 1;
                operation
            }
        };
        tally.shape(operation);
        for (r, honest) in [(root, true), (wrong, false)] {
            let (expected, actual) = exclusion(&proof, &k, &r);
            assert_eq!(expected, honest, "production, absent key {seed}");
            assert_eq!(actual, expected, "client, absent key {seed}");
            tally.claims += 1;
        }
        // The same proof for each live key, which no exclusion proof may cover.
        for &other in live.iter().take(3) {
            let (expected, actual) = exclusion(&proof, &key(other), &root);
            assert!(!expected, "production, live key {other}");
            assert_eq!(actual, expected, "client, live key {other}");
            tally.claims += 1;
        }
        if j % tamper != 0 {
            continue;
        }
        let mut altered: Vec<(String, _)> = tamperings(operation)
            .into_iter()
            .map(|(name, op)| {
                let proof = match &proof {
                    production::proof::ExclusionProof::KeyValue(_, update) => {
                        production::proof::ExclusionProof::KeyValue(op, update.clone())
                    }
                    production::proof::ExclusionProof::Commit(_, metadata) => {
                        production::proof::ExclusionProof::Commit(op, metadata.clone())
                    }
                };
                (name, proof)
            })
            .collect();
        match &proof {
            production::proof::ExclusionProof::KeyValue(op, update) => {
                for (name, field) in [
                    ("update key", 0),
                    ("update value", 1),
                    ("update next key", 2),
                ] {
                    let mut update = update.clone();
                    match field {
                        0 => update.key = key(seed + 1_000_000),
                        1 => update.value = value(seed + 1_000_000),
                        _ => update.next_key = key(seed + 1_000_001),
                    }
                    altered.push((
                        name.into(),
                        production::proof::ExclusionProof::KeyValue(op.clone(), update),
                    ));
                }
            }
            production::proof::ExclusionProof::Commit(op, metadata) => {
                let other = match metadata {
                    Some(_) => None,
                    None => Some(value(1_000_000)),
                };
                altered.push((
                    "commit metadata".into(),
                    production::proof::ExclusionProof::Commit(op.clone(), other),
                ));
            }
        }
        for (name, altered) in altered {
            let (expected, actual) = exclusion(&altered, &k, &root);
            assert!(!expected, "production, absent key {seed}, {name}");
            assert_eq!(actual, expected, "client, absent key {seed}, {name}");
            tally.tampered += 1;
        }
    }
}

#[test]
fn reads_agree_with_production() {
    deterministic::Runner::default().start(|context| async move {
        let mut tally = Tally::default();
        for size in [1u64, 9, 300, 450] {
            let db = open(context.child("db"), &format!("size-{size}")).await;
            let live: Vec<u64> = (0..size).map(|i| 2 * i + 2).collect();
            let db = apply(db, live.iter().map(|&s| (key(s), Some(value(s)))).collect()).await;
            let probes: Vec<u64> = (0..12).map(|i| i * (2 * size + 4) / 11).collect();
            check(&db, &live, &probes, 37, &mut tally).await;
            db.destroy().await.unwrap();
        }
        assert!(tally.claims > 1000, "only {} claims checked", tally.claims);
        assert!(tally.tampered > 1000, "only {} tamperings", tally.tampered);
    });
}

#[test]
fn reads_agree_with_production_across_histories() {
    deterministic::Runner::default().start(|context| async move {
        let mut rng = test_rng();
        let mut tally = Tally::default();
        let mut db = open(context.child("db"), "history").await;
        let mut live = BTreeMap::new();
        for round in 0..12u64 {
            let mut writes = BTreeMap::new();
            for _ in 0..rng.random_range(1..80) {
                let seed = 2 * rng.random_range(1..200u64);
                let write = if live.contains_key(&seed) && rng.random_bool(0.4) {
                    None
                } else {
                    Some(value(1_000 * round + seed))
                };
                writes.insert(seed, write);
            }
            for (&seed, write) in &writes {
                match write {
                    Some(v) => live.insert(seed, v.clone()),
                    None => live.remove(&seed),
                };
            }
            db = apply(db, writes.into_iter().map(|(s, w)| (key(s), w)).collect()).await;
            let seeds: Vec<u64> = live.keys().copied().collect();
            for &seed in &seeds {
                assert_eq!(db.get(&key(seed)).await.unwrap(), live.get(&seed).cloned());
            }
            let probes: Vec<u64> = (0..40).map(|i| 2 * i + 1).chain([0, 1_000]).collect();
            check(&db, &seeds, &probes, 11, &mut tally).await;
        }
        db.destroy().await.unwrap();
        assert!(tally.tampered > 1000, "only {} tamperings", tally.tampered);
        assert!(tally.pending > 0, "no proof had a pending chunk");
        assert!(tally.partial > 0, "no proof had a partial chunk");
        assert!(tally.inactive > 0, "no proof had inactive peaks");
    });
}

#[test]
fn empty_reads_agree_with_production() {
    deterministic::Runner::default().start(|context| async move {
        let db = open(context.child("db"), "empty").await;
        let seeds = [2u64, 4, 6];
        let db = apply(
            db,
            seeds.iter().map(|&s| (key(s), Some(value(s)))).collect(),
        )
        .await;
        let db = apply(db, seeds.iter().map(|&s| (key(s), None)).collect()).await;
        let mut tally = Tally::default();
        check(&db, &[], &[0, 1, 2, 3, 7, 100], 1, &mut tally).await;
        assert!(tally.claims > 0);
        assert!(tally.commit > 0, "no exclusion proof was a commit");
        db.destroy().await.unwrap();
    });
}
