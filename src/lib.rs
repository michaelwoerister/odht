//! This crate implements a hash table that can be used as is in its binary, on-disk format.
//! The goal is to provide a high performance data structure that can be used without any significant up-front decoding.
//! The implementation makes no assumptions about alignment or endianess of the underlying data,
//! so a table encoded on one platform can be used on any other platform and
//! the binary data can be mapped into memory at arbitrary addresses.
//!
//!
//! ## Usage
//!
//! In order to use the hash table one needs to implement the `Config` trait.
//! This trait defines how the table is encoded and what hash function is used.
//! With a `Config` in place the `HashTableOwned` type can be used to build and serialize a hash table.
//! The `HashTable` type can then be used to create an almost zero-cost view of the serialized hash table.
//!
//! ```rust
//!
//! use odht::{HashTable, HashTableOwned, Config, FxHashFn};
//!
//! struct MyConfig;
//!
//! impl Config for MyConfig {
//!
//!     type Key = u64;
//!     type Value = u32;
//!
//!     type EncodedKey = [u8; 8];
//!     type EncodedValue = [u8; 4];
//!
//!     type H = FxHashFn;
//!
//!     #[inline] fn encode_key(k: &Self::Key) -> Self::EncodedKey { k.to_le_bytes() }
//!     #[inline] fn encode_value(v: &Self::Value) -> Self::EncodedValue { v.to_le_bytes() }
//!     #[inline] fn decode_key(k: &Self::EncodedKey) -> Self::Key { u64::from_le_bytes(*k) }
//!     #[inline] fn decode_value(v: &Self::EncodedValue) -> Self::Value { u32::from_le_bytes(*v)}
//! }
//!
//! fn main() {
//!     let mut builder = HashTableOwned::<MyConfig>::with_capacity(3, 95);
//!
//!     builder.insert(&1, &2);
//!     builder.insert(&3, &4);
//!     builder.insert(&5, &6);
//!
//!     let serialized: Vec<u8> = {
//!         let mut data = std::io::Cursor::new(Vec::new());
//!         builder.serialize(&mut data).unwrap();
//!         data.into_inner()
//!     };
//!
//!     let table = HashTable::<MyConfig>::from_serialized(&serialized[..]).unwrap();
//!
//!     assert_eq!(table.get(&1), Some(2));
//!     assert_eq!(table.get(&3), Some(4));
//!     assert_eq!(table.get(&5), Some(6));
//! }
//! ```

#![cfg_attr(feature = "nightly", feature(core_intrinsics))]

mod error;
mod fxhash;
mod raw_table;
mod serialize;
mod unhash;

pub use crate::fxhash::FxHashFn;
pub use crate::unhash::UnHashFn;

use crate::raw_table::{ByteArray, Entry, EntryMetadata, RawIter, RawTable, RawTableMut};
use std::io::Cursor;
use std::marker::PhantomData;

/// This trait provides a complete "configuration" for a hash table, i.e. it
/// defines the key and value types, how these are encoded and what hash
/// function is being used.
///
/// Implementations of the `encode_key` and `encode_value` methods must encode
/// the given key/value into a fixed size array. The encoding must be
/// deterministic (i.e. no random padding bytes) and must be independent of
/// platform endianess. It is always highly recommended to mark these methods
/// as #[inline].
pub trait Config {
    type Key;
    type Value;

    // The EncodedKey and EncodedValue types must always be a fixed size array of bytes,
    // e.g. [u8; 4].
    type EncodedKey: ByteArray;
    type EncodedValue: ByteArray;

    type H: HashFn;

    /// Implementations of the `encode_key` and `encode_value` methods must encode
    /// the given key/value into a fixed size array. See above for requirements.
    fn encode_key(k: &Self::Key) -> Self::EncodedKey;

    /// Implementations of the `encode_key` and `encode_value` methods must encode
    /// the given key/value into a fixed size array. See above for requirements.
    fn encode_value(v: &Self::Value) -> Self::EncodedValue;

    fn decode_key(k: &Self::EncodedKey) -> Self::Key;
    fn decode_value(v: &Self::EncodedValue) -> Self::Value;
}

/// This trait represents hash functions as used by HashTable and
/// HashTableOwned.
pub trait HashFn: Eq {
    fn hash(bytes: &[u8]) -> u32;
}

/// `HashTableOwned` is used building and then persisting hash tables. It
/// does provide methods for looking up values but
pub struct HashTableOwned<C: Config> {
    _config: PhantomData<C>,
    entry_metadata: Vec<EntryMetadata>,
    entry_data: Vec<Entry<C::EncodedKey, C::EncodedValue>>,
    mod_mask: usize,

    max_item_count: usize,
    item_count: usize,

    // We use integer math here as not to run into any issues with
    // platform-specific floating point math implementation.
    max_load_factor_percent: u8,
}

impl<C: Config> HashTableOwned<C> {
    pub fn with_capacity(item_count: usize, max_load_factor_percent: u8) -> HashTableOwned<C> {
        assert!(max_load_factor_percent <= 100);
        assert!(max_load_factor_percent > 0);

        let slots_needed = slots_needed(item_count, max_load_factor_percent);
        let slots_needed = slots_needed.checked_next_power_of_two().unwrap();
        assert!(slots_needed > 0);

        let mod_mask = slots_needed.checked_sub(1).unwrap();
        let max_item_count = max_item_count(slots_needed, max_load_factor_percent);

        HashTableOwned {
            _config: PhantomData::default(),
            entry_metadata: vec![EntryMetadata::default(); slots_needed],
            entry_data: vec![Entry::default(); slots_needed],
            mod_mask,
            max_load_factor_percent,
            max_item_count,
            item_count: 0,
        }
    }

    /// Retrieves the value for the given key. Returns `None` if no entry is found.
    #[inline]
    pub fn get(&self, key: &C::Key) -> Option<C::Value> {
        let encoded_key = C::encode_key(key);
        self.as_raw().find(&encoded_key).map(C::decode_value)
    }

    /// Inserts the given key-value pair into the table.
    /// Grows the table if necessary.
    #[inline]
    pub fn insert(&mut self, key: &C::Key, value: &C::Value) -> Option<C::Value> {
        if self.item_count == self.max_item_count {
            self.grow();
        }

        assert!(self.item_count < self.max_item_count);

        let encoded_key = C::encode_key(key);
        let raw_value = C::encode_value(value);

        if let Some(old_value) = self.as_raw_mut().insert(encoded_key, raw_value) {
            Some(C::decode_value(&old_value))
        } else {
            self.item_count += 1;
            None
        }
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, C> {
        Iter(RawIter::new(&self.entry_metadata[..], &self.entry_data[..]))
    }

    pub fn from_iterator<I: IntoIterator<Item = (C::Key, C::Value)>>(
        it: I,
        max_load_factor_percent: u8,
    ) -> Self {
        let it = it.into_iter();

        let known_size = match it.size_hint() {
            (min, Some(max)) => {
                if min == max {
                    Some(max)
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some(known_size) = known_size {
            let mut table = HashTableOwned::with_capacity(known_size, max_load_factor_percent);

            let initial_slot_count = table.entry_data.len();

            for (k, v) in it {
                table.insert(&k, &v);
            }

            assert_eq!(table.len(), known_size);
            assert_eq!(table.entry_data.len(), initial_slot_count);

            table
        } else {
            let items: Vec<_> = it.collect();
            Self::from_iterator(items, max_load_factor_percent)
        }
    }

    #[inline]
    fn as_raw(&self) -> RawTable<'_, C::EncodedKey, C::EncodedValue, C::H> {
        RawTable::new(
            &self.entry_metadata[..],
            &self.entry_data[..],
            self.mod_mask,
        )
    }

    #[inline]
    fn as_raw_mut(&mut self) -> RawTableMut<'_, C::EncodedKey, C::EncodedValue, C::H> {
        RawTableMut::new(
            &mut self.entry_metadata[..],
            &mut self.entry_data[..],
            self.mod_mask,
        )
    }

    #[inline(never)]
    #[cold]
    fn grow(&mut self) {
        let mut new_table = Self::with_capacity(self.item_count * 2, self.max_load_factor_percent);

        {
            let mut new_table = new_table.as_raw_mut();

            for (entry_metadata, entry_data) in self.as_raw().iter() {
                new_table.insert_entry(entry_metadata, *entry_data);
            }
        }

        *self = new_table;
    }

    pub fn serialize(&self, w: &mut dyn std::io::Write) -> Result<(), Box<dyn std::error::Error>> {
        serialize::serialize::<C>(
            &self.entry_metadata,
            &self.entry_data,
            self.item_count,
            self.max_load_factor_percent,
            w,
        )
    }

    pub fn serialize_to_vec(&self) -> Vec<u8> {
        let bytes_needed = serialize::bytes_needed::<C>(self.entry_metadata.len());
        let mut cursor = Cursor::new(Vec::with_capacity(bytes_needed));
        self.serialize(&mut cursor).unwrap();
        cursor.into_inner()
    }

    pub fn from_serialized(data: &[u8]) -> Result<HashTableOwned<C>, Box<dyn std::error::Error>> {
        let (header, entry_metadata, entry_data) = serialize::deserialize::<C>(data)?;

        let max_load_factor_percent = header.max_load_factor_percent();

        Ok(HashTableOwned {
            _config: PhantomData::default(),
            entry_metadata: entry_metadata.to_owned(),
            entry_data: entry_data.to_owned(),
            mod_mask: header.mod_mask(),
            item_count: header.item_count(),
            max_load_factor_percent,
            max_item_count: max_item_count(header.slot_count(), max_load_factor_percent),
        })
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.item_count
    }
}

impl<C: Config> std::fmt::Debug for HashTableOwned<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "(item_count={}, mod_mask={:x}, max_item_count={}, max_load_factor={})",
            self.item_count, self.mod_mask, self.max_item_count, self.max_load_factor_percent
        )?;

        writeln!(f, "{:?}", self.as_raw())
    }
}

/// This type provides a cheap to construct readonly view on a persisted
/// hash table.
pub struct HashTable<'a, C: Config> {
    _config: PhantomData<C>,
    entry_metadata: &'a [EntryMetadata],
    entry_data: &'a [Entry<C::EncodedKey, C::EncodedValue>],
    mod_mask: usize,
    item_count: usize,
}

impl<'a, C: Config> HashTable<'a, C> {
    pub fn from_serialized(data: &[u8]) -> Result<HashTable<'_, C>, Box<dyn std::error::Error>> {
        let (header, entry_metadata, entry_data) = serialize::deserialize::<C>(data)?;

        Ok(HashTable {
            _config: PhantomData::default(),
            entry_metadata,
            entry_data,
            mod_mask: header.mod_mask(),
            item_count: header.item_count(),
        })
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.item_count
    }

    #[inline]
    pub fn get(&self, key: &C::Key) -> Option<C::Value> {
        let encoded_key = C::encode_key(key);
        self.as_raw().find(&encoded_key).map(C::decode_value)
    }

    #[inline]
    fn as_raw(&self) -> RawTable<'_, C::EncodedKey, C::EncodedValue, C::H> {
        RawTable::new(self.entry_metadata, self.entry_data, self.mod_mask)
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_, C> {
        Iter(RawIter::new(self.entry_metadata, self.entry_data))
    }
}

pub struct Iter<'a, C: Config>(RawIter<'a, C::EncodedKey, C::EncodedValue>);

impl<'a, C: Config> Iterator for Iter<'a, C> {
    type Item = (C::Key, C::Value);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, entry)| {
            let key = C::decode_key(&entry.key);
            let value = C::decode_value(&entry.value);

            (key, value)
        })
    }
}

fn slots_needed(item_count: usize, max_load_factor_percent: u8) -> usize {
    let max_load_factor_percent = max_load_factor_percent as usize;
    // Note: we round up here
    (100 * item_count + max_load_factor_percent - 1) / max_load_factor_percent
}

fn max_item_count(capacity: usize, max_load_factor_percent: u8) -> usize {
    let max_load_factor_percent = max_load_factor_percent as usize;
    // Note: we round down here
    (max_load_factor_percent * capacity) / 100
}

#[cfg(test)]
mod tests {

    use std::{convert::TryInto, io::Cursor};

    use super::*;

    enum TestConfig {}

    impl Config for TestConfig {
        type EncodedKey = [u8; 4];
        type EncodedValue = [u8; 4];

        type Key = u32;
        type Value = u32;

        type H = FxHashFn;

        fn encode_key(k: &Self::Key) -> Self::EncodedKey {
            k.to_le_bytes()
        }

        fn encode_value(v: &Self::Value) -> Self::EncodedValue {
            v.to_le_bytes()
        }

        fn decode_key(k: &Self::EncodedKey) -> Self::Key {
            u32::from_le_bytes(k[..].try_into().unwrap())
        }

        fn decode_value(v: &Self::EncodedValue) -> Self::Value {
            u32::from_le_bytes(v[..].try_into().unwrap())
        }
    }

    fn make_test_items(count: usize) -> Vec<(u32, u32)> {
        if count == 0 {
            return vec![];
        }

        let mut items = vec![];

        if count > 1 {
            let steps = (count - 1) as u32;
            let step = u32::MAX / steps;

            for i in 0..steps {
                let x = i * step;
                items.push((x, u32::MAX - x));
            }
        }

        items.push((u32::MAX, 0));

        items.sort();
        items.dedup();
        assert_eq!(items.len(), count);

        items
    }

    #[test]
    fn from_iterator() {
        for count in 0..33 {
            let items = make_test_items(count);
            let table = HashTableOwned::<TestConfig>::from_iterator(items.clone(), 95);
            assert_eq!(table.len(), items.len());

            let mut actual_items: Vec<_> = table.iter().collect();
            actual_items.sort();

            assert_eq!(items, actual_items);
        }
    }

    #[test]
    fn hash_table_at_different_alignments() {
        let items = make_test_items(33);

        let mut serialized = {
            let table: HashTableOwned<TestConfig> =
                HashTableOwned::from_iterator(items.clone(), 95);

            assert_eq!(table.len(), items.len());

            let mut stream = Cursor::new(Vec::new());

            table.serialize(&mut stream).unwrap();

            stream.into_inner()
        };

        for alignment_shift in 0..4 {
            let data = &serialized[alignment_shift..];

            let table = HashTable::<TestConfig>::from_serialized(data).unwrap();

            assert_eq!(table.len(), items.len());

            for (key, value) in items.iter() {
                assert_eq!(table.get(key), Some(*value));
            }

            serialized.insert(0, 0xFFu8);
        }
    }

    #[test]
    fn load_factor_and_item_count() {
        assert_eq!(slots_needed(0, 100), 0);
        assert_eq!(slots_needed(6, 60), 10);
        assert_eq!(slots_needed(5, 50), 10);
        assert_eq!(slots_needed(5, 49), 11);
        assert_eq!(slots_needed(1000, 100), 1000);

        assert_eq!(max_item_count(1, 100), 1);
        assert_eq!(max_item_count(10, 50), 5);
        assert_eq!(max_item_count(11, 50), 5);
        assert_eq!(max_item_count(12, 50), 6);
    }
}
