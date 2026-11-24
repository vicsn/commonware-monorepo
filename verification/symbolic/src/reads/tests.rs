//! Differential tests of the reads client against production: current ordered databases over an
//! MMB with 32-byte keys and values, whose key-value and exclusion proofs production's
//! `KeyValueProof::verify` and `ExclusionProof::verify` check. On every honest proof and on
//! altered ones (another value, another successor, another root, another key) the client must
//! return production's verdict, and every honest proof must be accepted.

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
use commonware_utils::{NZU16, NZU64, NZUsize, sequence::FixedBytes};

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

/// Check every live key, and the keys between and beyond them, of `db`, whose live keys are
/// `live` in order.
async fn check(db: &Database, live: &[u64], probes: &[u64]) -> usize {
    let root = db.root();
    let wrong = other_root(&root);
    let mut checked = 0;
    for (i, &seed) in live.iter().enumerate() {
        let k = key(seed);
        let (proof, v) = db.key_value_proof(&k).await.unwrap();
        let next = key(live[(i + 1) % live.len()]);
        assert_eq!(proof.next_key, next);
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
            checked += 1;
        }
    }
    for &seed in probes {
        let k = key(seed);
        if live.contains(&seed) {
            continue;
        }
        let proof = db.exclusion_proof(&k).await.unwrap();
        for (r, honest) in [(root, true), (wrong, false)] {
            let (expected, actual) = exclusion(&proof, &k, &r);
            assert_eq!(expected, honest, "production, absent key {seed}");
            assert_eq!(actual, expected, "client, absent key {seed}");
            checked += 1;
        }
        // The same proof for each live key, which no exclusion proof may cover.
        for &other in live.iter().take(3) {
            let (expected, actual) = exclusion(&proof, &key(other), &root);
            assert!(!expected, "production, live key {other}");
            assert_eq!(actual, expected, "client, live key {other}");
            checked += 1;
        }
    }
    checked
}

#[test]
fn reads_agree_with_production() {
    deterministic::Runner::default().start(|context| async move {
        let mut checked = 0;
        for size in [1u64, 9, 300, 450] {
            let db = open(context.child("db"), &format!("size-{size}")).await;
            let live: Vec<u64> = (0..size).map(|i| 2 * i + 2).collect();
            let db = apply(db, live.iter().map(|&s| (key(s), Some(value(s)))).collect()).await;
            let probes: Vec<u64> = (0..12).map(|i| i * (2 * size + 4) / 11).collect();
            checked += check(&db, &live, &probes).await;
            db.destroy().await.unwrap();
        }
        assert!(checked > 1000, "only {checked} claims checked");
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
        let checked = check(&db, &[], &[0, 1, 2, 3, 7, 100]).await;
        assert!(checked > 0);
        db.destroy().await.unwrap();
    });
}
