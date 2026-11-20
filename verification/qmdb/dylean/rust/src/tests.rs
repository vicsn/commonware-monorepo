//! Differential tests of the client against the production MMR.
//!
//! The client, which runs the production traversal and encodings, and the production
//! `Proof::verify_element_inclusion` must return the same verdict on honest openings and on
//! substituted, misplaced, reordered, short and long ones. Honest production openings must verify
//! under the production root, which is the snapshot assumption of the Lean proofs.

use crate::{
    client::{self, Messages},
    terms::{Part, Terms},
};
use commonware_cryptography::{Hasher as _, Sha256, sha256};
use commonware_storage::merkle::{
    Bagging,
    mmr::{Location, Proof, StandardHasher, mem::Mmr},
};
use commonware_utils::test_rng;
use rand::RngExt as _;

/// Concrete terms: parts concatenated and hashed with SHA-256.
struct Concrete;

impl Terms for Concrete {
    type Digest = [u8; 32];

    fn hash(&self, parts: &[Part<'_, [u8; 32]>]) -> [u8; 32] {
        let mut input = Vec::new();
        for part in parts {
            match part {
                Part::Bytes(part) => input.extend_from_slice(part),
                Part::Digest(digest) => input.extend_from_slice(*digest),
            }
        }
        bytes(&Sha256::hash(&[&input]))
    }
}

impl Messages for Concrete {
    type Message = Vec<u8>;

    fn parse<'a>(&self, message: &'a Vec<u8>) -> Option<&'a [u8]> {
        Some(message)
    }
}

fn bytes(digest: &sha256::Digest) -> [u8; 32] {
    digest.as_ref().try_into().unwrap()
}

fn tamper(digest: &sha256::Digest) -> sha256::Digest {
    Sha256::hash(&[b"tamper", digest.as_ref()])
}

type Production = StandardHasher<Sha256>;

fn production(items: &[Vec<u8>]) -> (Production, Mmr<sha256::Digest>) {
    let hasher = Production::new(Bagging::ForwardFold);
    let mut mmr = Mmr::new();
    let batch = {
        let mut batch = mmr.new_batch();
        for item in items {
            batch = batch.add(&hasher, item);
        }
        batch.merkleize(&mmr, &hasher)
    };
    mmr.apply_batch(&batch).unwrap();
    (hasher, mmr)
}

fn random_items(rng: &mut impl rand::Rng, count: u64) -> Vec<Vec<u8>> {
    (0..count)
        .map(|_| {
            let mut item = vec![0u8; rng.random_range(0..40usize)];
            rng.fill_bytes(&mut item);
            item
        })
        .collect()
}

/// One inclusion claim with its expected verdict.
struct Claim {
    name: &'static str,
    location: u64,
    item: Vec<u8>,
    digests: Vec<sha256::Digest>,
    root: sha256::Digest,
    honest: bool,
}

/// The honest claim for `location` and its mutations.
fn claims(
    items: &[Vec<u8>],
    location: u64,
    digests: &[sha256::Digest],
    root: sha256::Digest,
) -> Vec<Claim> {
    let leaves = items.len() as u64;
    let item = items[location as usize].clone();
    let claim = |name, location, item: &Vec<u8>, digests: Vec<_>, root, honest| Claim {
        name,
        location,
        item: item.clone(),
        digests,
        root,
        honest,
    };
    let mut claims = vec![claim(
        "honest",
        location,
        &item,
        digests.to_vec(),
        root,
        true,
    )];
    let mut longer = item.clone();
    longer.push(0);
    claims.push(claim(
        "item",
        location,
        &longer,
        digests.to_vec(),
        root,
        false,
    ));
    claims.push(claim(
        "root",
        location,
        &item,
        digests.to_vec(),
        Sha256::hash(&[b"other root"]),
        false,
    ));
    claims.push(claim(
        "out of range",
        leaves,
        &item,
        digests.to_vec(),
        root,
        false,
    ));
    let mut extra = digests.to_vec();
    extra.push(Sha256::hash(&[b"extra"]));
    claims.push(claim("long", location, &item, extra, root, false));
    if leaves > 1 {
        let other = (location + 1) % leaves;
        if items[other as usize] != item {
            claims.push(claim(
                "misplaced",
                other,
                &item,
                digests.to_vec(),
                root,
                false,
            ));
        }
        let mut short = digests.to_vec();
        short.pop();
        claims.push(claim("short", location, &item, short, root, false));
        for index in 0..digests.len() {
            let mut substituted = digests.to_vec();
            substituted[index] = tamper(&digests[index]);
            claims.push(claim(
                "substituted",
                location,
                &item,
                substituted,
                root,
                false,
            ));
        }
    }
    if digests.len() > 1 {
        let mut swapped = digests.to_vec();
        swapped.swap(0, 1);
        claims.push(claim("swapped", location, &item, swapped, root, false));
    }
    claims
}

#[test]
fn production_openings_verify() {
    let mut rng = test_rng();
    for height in 0..=8u32 {
        let leaves = 1u64 << height;
        let items = random_items(&mut rng, leaves);
        let (hasher, mmr) = production(&items);
        let root = bytes(&mmr.root(&hasher, 0).unwrap());
        for location in 0..leaves {
            let proof = mmr.proof(&hasher, Location::new(location), 0).unwrap();
            let siblings: Vec<_> = proof.digests.iter().map(bytes).collect();
            assert!(
                client::verify(
                    &Concrete,
                    height,
                    location,
                    &root,
                    &items[location as usize],
                    &siblings
                ),
                "height {height}, location {location}"
            );
        }
    }
}

#[test]
fn verifiers_agree_with_production() {
    let mut rng = test_rng();
    let mut checked = 0;
    for height in 0..=6u32 {
        let leaves = 1u64 << height;
        let items = random_items(&mut rng, leaves);
        let (hasher, mmr) = production(&items);
        let root = mmr.root(&hasher, 0).unwrap();
        for location in 0..leaves {
            let proof = mmr.proof(&hasher, Location::new(location), 0).unwrap();
            assert_eq!(proof.inactive_peaks, 0);
            for claim in claims(&items, location, &proof.digests, root) {
                let siblings: Vec<_> = claim.digests.iter().map(bytes).collect();
                let claimed = Proof {
                    leaves: proof.leaves,
                    inactive_peaks: 0,
                    digests: claim.digests.clone(),
                };
                let expected = claimed.verify_element_inclusion(
                    &hasher,
                    Location::new(claim.location),
                    &claim.item,
                    &claim.root,
                );
                let context = format!("height {height}, location {location}, {}", claim.name);
                assert_eq!(expected, claim.honest, "production: {context}");
                let root = bytes(&claim.root);
                assert_eq!(
                    client::verify(
                        &Concrete,
                        height,
                        claim.location,
                        &root,
                        &claim.item,
                        &siblings
                    ),
                    expected,
                    "verify: {context}"
                );
                let accepted = client::client_step(
                    &Concrete,
                    &root,
                    height,
                    &claim.item,
                    claim.location,
                    &siblings,
                );
                assert_eq!(accepted.is_some(), expected, "client: {context}");
                if let Some(event) = accepted {
                    assert_eq!(event.height, height);
                    assert_eq!(event.location, claim.location);
                    assert_eq!(event.item, claim.item);
                }
                checked += 1;
            }
        }
    }
    assert!(checked > 1000, "only {checked} claims checked");
}

#[test]
fn client_rejects_heights_above_the_bound() {
    let message = vec![1];
    for height in [client::MAX_HEIGHT + 1, u32::MAX] {
        assert!(
            client::client_step(&Concrete, &[0; 32], height, &message, 0, &[]).is_none(),
            "height {height}"
        );
    }
}
