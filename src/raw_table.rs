//! This module implements the actual hash table logic. It works solely with
//! byte arrays and does not know anything about the unencoded key and value
//! types.
//!
//! The implementation makes sure that the encoded data contains no padding
//! bytes (which makes it deterministic) and nothing in it requires any specific
//! alignment.
//!
//! Many functions in this module are marked as `#[inline]`. This is allows
//! LLVM to retain the information about byte array sizes, even though they are
//! converted to slices (of unknown size) from time to time.
//!
//! The implementation uses robin hood hashing with linear probing and is based
//! mostly on [Robin Hood Hashing should be your default Hash Table
//! implementation][rhh] by Sebastian Sylvan.
//!
//! [rhh]: https://www.sebastiansylvan.com/post/robin-hood-hashing-should-be-your-default-hash-table-implementation/

use crate::{error::Error, HashFn};
use std::{
    fmt,
    marker::PhantomData,
    mem::{align_of, size_of},
};

#[cfg(feature = "nightly")]
macro_rules! likely {
    ($x:expr) => {
        core::intrinsics::likely($x)
    };
}

#[cfg(not(feature = "nightly"))]
macro_rules! likely {
    ($x:expr) => {
        $x
    };
}

/// Values of this type represent key-value pairs *as they are stored on-disk*.
/// `#[repr(C)]` makes sure we have deterministic field order and the fields
/// being byte arrays makes sure that there are no padding bytes, alignment is
/// not restricted, and the data is endian-independent.
///
/// It is a strict requirement that any `&[Entry<K, V>]` can be transmuted
/// into a `&[u8]` and back, regardless of whether the byte array has been
/// moved in the meantime.
#[repr(C)]
#[derive(PartialEq, Eq, Default, Clone, Copy, Debug)]
pub(crate) struct Entry<K: ByteArray, V: ByteArray> {
    pub key: K,
    pub value: V,
}

impl<K: ByteArray, V: ByteArray> Entry<K, V> {
    #[inline]
    fn new(key: K, value: V) -> Entry<K, V> {
        Entry { key, value }
    }
}

impl<'a, K: ByteArray, V: ByteArray, H: HashFn> fmt::Debug for RawTable<'a, K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut probe_distances = Vec::new();

        for (i, (metadata, entry)) in self.metadata.iter().zip(self.data.iter()).enumerate() {
            if metadata.is_empty() {
                writeln!(f, "{:>2} -", i)?;
            } else {
                let probe_distance = probe_distance(metadata.hash(), i, self.mod_mask);
                probe_distances.push(probe_distance);

                writeln!(
                    f,
                    "{:>2} - desired={:>2}, dist={:>2}, key: {:?}, val: {:?}",
                    i,
                    desired_index(metadata.hash(), self.mod_mask),
                    probe_distance,
                    entry.key,
                    entry.value
                )?;
            }
        }

        if probe_distances.is_empty() {
            return writeln!(f, "");
        }

        let max_probe_distance = probe_distances.iter().cloned().max().unwrap();
        let average_probe_distance =
            probe_distances.iter().cloned().sum::<usize>() as f32 / probe_distances.len() as f32;

        let mut probe_distance_histogram = vec![0; max_probe_distance + 1];

        for probe_distance in probe_distances {
            probe_distance_histogram[probe_distance] += 1;
        }

        writeln!(f, "\nstats:")?;
        writeln!(f, "  - average probe distance = {}", average_probe_distance)?;
        writeln!(f, "  - max probe distance = {}", max_probe_distance)?;
        writeln!(
            f,
            "  - probe distance histogram = {:?}",
            probe_distance_histogram
        )
    }
}

/// `EntryMetadata` stores the hash value of a given entry. A value of zero
/// denotes an empty entry. The `make_hash` function below makes sure that
/// all actual hash values are non-zero.
#[repr(C)]
#[derive(PartialEq, Eq, Default, Clone, Copy, Debug)]
pub(crate) struct EntryMetadata {
    hash: [u8; 4],
}

impl EntryMetadata {
    #[inline]
    fn occupied(hash: u32) -> EntryMetadata {
        assert!(align_of::<EntryMetadata>() == 1);

        // We expect the hash value of occupied entries to be non-zero.
        debug_assert!(hash != 0);
        EntryMetadata {
            hash: hash.to_le_bytes(),
        }
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.hash == [0, 0, 0, 0]
    }

    #[inline]
    fn hash(&self) -> u32 {
        debug_assert!(!self.is_empty());
        u32::from_le_bytes(self.hash)
    }
}

/// Computes the hash value of the given key, making sure that the result is
/// always non-zero.
#[inline]
fn make_hash<K: ByteArray, H: HashFn>(key: &K) -> u32 {
    let hash = H::hash(key.as_slice());
    hash | (1 << 31)
}

/// Computes the index a key with the given hash should ideally, i.e. if
/// that slot was not occupied by another entry.
#[inline]
fn desired_index(hash: u32, mod_mask: usize) -> usize {
    (hash as usize) & mod_mask
}

/// Computes how far a key with the given hash is away from its desired
/// index. The formula works even if probing wrapped around the end of
/// the table.
/// From https://gist.github.com/ssylvan/5538011
#[inline]
fn probe_distance(hash: u32, slot_index: usize, mod_mask: usize) -> usize {
    let slot_count = mod_mask + 1;
    debug_assert!(slot_count.is_power_of_two());
    (slot_index + slot_count - desired_index(hash, mod_mask)) & mod_mask
}

/// This type provides a readonly view of the given table data.
#[derive(PartialEq, Eq)]
pub(crate) struct RawTable<'a, K, V, H>
where
    K: ByteArray,
    V: ByteArray,
    H: HashFn,
{
    metadata: &'a [EntryMetadata],
    data: &'a [Entry<K, V>],
    mod_mask: usize,
    _hash_fn: PhantomData<H>,
}

impl<'a, K, V, H> RawTable<'a, K, V, H>
where
    K: ByteArray,
    V: ByteArray,
    H: HashFn,
{
    #[inline]
    pub(crate) fn new(
        metadata: &'a [EntryMetadata],
        data: &'a [Entry<K, V>],
        mod_mask: usize,
    ) -> Self {
        // Make sure Entry<K, V> does not contain any padding bytes and can be
        // stored at arbitrary adresses.
        assert!(size_of::<Entry<K, V>>() == size_of::<K>() + size_of::<V>());
        assert!(std::mem::align_of::<Entry<K, V>>() == 1);

        debug_assert!((mod_mask + 1).is_power_of_two());

        Self {
            metadata,
            data,
            mod_mask,
            _hash_fn: PhantomData::default(),
        }
    }

    #[inline]
    pub(crate) fn find(&self, key: &K) -> Option<&V> {
        let search_hash = make_hash::<K, H>(key);
        let mut i = desired_index(search_hash, self.mod_mask);
        let mut search_probe_distance = 0;

        loop {
            let h = self.metadata[i];

            if h.is_empty() {
                return None;
            }

            if h.hash() == search_hash {
                let entry = &self.data[i];

                if likely!(key.equals(&entry.key)) {
                    return Some(&entry.value);
                }
            }

            if search_probe_distance > probe_distance(h.hash(), i, self.mod_mask) {
                return None;
            }

            search_probe_distance += 1;
            i = (i + 1) & self.mod_mask;
        }
    }

    #[inline]
    pub(crate) fn iter(&'a self) -> RawIter<'a, K, V> {
        RawIter::new(self.metadata, self.data)
    }

    /// Check (for the first `entries_to_check` entries) if the computed and
    /// the stored hash value match.
    ///
    /// A mismatch is an indication that the table has been deserialized with
    /// the wrong hash function.
    pub(crate) fn sanity_check_hashes(&self, slots_to_check: usize) -> Result<(), Error> {
        let mut i = 0;
        let slots_to_check = std::cmp::min(slots_to_check, self.metadata.len());

        while i < slots_to_check {
            let hash = self.metadata[i];

            if !hash.is_empty() {
                let expected_hash = hash.hash();
                let actual_hash = make_hash::<K, H>(&self.data[i].key);

                if actual_hash != expected_hash {
                    let message = format!(
                        "Hash mismatch for entry {}. Expected {}, found {}.",
                        i, expected_hash, actual_hash
                    );

                    return Err(Error(message));
                }
            }

            i += 1;
        }

        Ok(())
    }
}

/// This type provides a mutable view of the given table data. It allows for
/// inserting new entries but does not allow for growing the table.
#[derive(PartialEq, Eq)]
pub(crate) struct RawTableMut<'a, K, V, H>
where
    K: ByteArray,
    V: ByteArray,
    H: HashFn,
{
    metadata: &'a mut [EntryMetadata],
    data: &'a mut [Entry<K, V>],
    mod_mask: usize,
    _hash_fn: PhantomData<H>,
}

impl<'a, K, V, H> RawTableMut<'a, K, V, H>
where
    K: ByteArray,
    V: ByteArray,
    H: HashFn,
{
    #[inline]
    pub(crate) fn new(
        metadata: &'a mut [EntryMetadata],
        data: &'a mut [Entry<K, V>],
        mod_mask: usize,
    ) -> Self {
        // Make sure Entry<K, V> does not contain any padding bytes and can be
        // stored at arbitrary adresses.
        assert!(size_of::<Entry<K, V>>() == size_of::<K>() + size_of::<V>());
        assert!(std::mem::align_of::<Entry<K, V>>() == 1);

        debug_assert!((mod_mask + 1).is_power_of_two());

        Self {
            metadata,
            data,
            mod_mask,
            _hash_fn: PhantomData::default(),
        }
    }

    /// Inserts the given key value pair into the hash table.
    ///
    /// WARNING: This method assumes that there is free space in the hash table
    ///          somewhere. If there isn't it will end up in an infinite loop.
    #[inline]
    pub(crate) fn insert(&mut self, key: K, value: V) -> Option<V> {
        let new_entry = Entry::new(key, value);
        let new_entry_metadata = EntryMetadata::occupied(make_hash::<K, H>(&key));
        self.insert_entry(new_entry_metadata, new_entry)
    }

    /// Inserts the given key value pair into the hash table.
    ///
    /// WARNING: This method assumes that there is free space in the hash table
    ///          somewhere. If there isn't it will end up in an infinite loop.
    #[inline]
    pub(crate) fn insert_entry(
        &mut self,
        mut new_entry_metadata: EntryMetadata,
        mut new_entry: Entry<K, V>,
    ) -> Option<V> {
        debug_assert!(!new_entry_metadata.is_empty());
        let mut i = desired_index(new_entry_metadata.hash(), self.mod_mask);
        let mut this_probe_distance = 0;

        loop {
            let hash_slot = &mut self.metadata[i];

            if hash_slot.is_empty() {
                *hash_slot = new_entry_metadata;
                self.data[i] = new_entry;
                debug_assert!(!hash_slot.is_empty());
                return None;
            } else if hash_slot.hash() == new_entry_metadata.hash() {
                let entry_slot = &mut self.data[i];

                if likely!(entry_slot.key.equals(&new_entry.key)) {
                    debug_assert!(hash_slot.hash() == new_entry_metadata.hash());
                    let old_value = entry_slot.value;
                    entry_slot.value = new_entry.value;
                    return Some(old_value);
                }
            }

            let other_probe_distance = probe_distance(hash_slot.hash(), i, self.mod_mask);

            if this_probe_distance > other_probe_distance {
                std::mem::swap(&mut self.data[i], &mut new_entry);
                std::mem::swap(hash_slot, &mut new_entry_metadata);
                this_probe_distance = other_probe_distance;
            }

            this_probe_distance += 1;
            i = (i + 1) & self.mod_mask;
        }
    }
}

impl<'a, K: ByteArray, V: ByteArray, H: HashFn> fmt::Debug for RawTableMut<'a, K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let readonly = RawTable::<'_, K, V, H>::new(self.metadata, self.data, self.mod_mask);
        write!(f, "{:?}", readonly)
    }
}

pub(crate) struct RawIter<'a, K, V>
where
    K: ByteArray,
    V: ByteArray,
{
    metadata: &'a [EntryMetadata],
    data: &'a [Entry<K, V>],
    current_index: usize,
}

impl<'a, K, V> RawIter<'a, K, V>
where
    K: ByteArray,
    V: ByteArray,
{
    pub(crate) fn new(metadata: &'a [EntryMetadata], data: &'a [Entry<K, V>]) -> RawIter<'a, K, V> {
        debug_assert!(metadata.len() == data.len());
        debug_assert!(metadata.len().is_power_of_two());
        RawIter {
            metadata,
            data,
            current_index: 0,
        }
    }
}

impl<'a, K, V> Iterator for RawIter<'a, K, V>
where
    K: ByteArray,
    V: ByteArray,
{
    type Item = (EntryMetadata, &'a Entry<K, V>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.current_index == self.data.len() {
                return None;
            }

            let index = self.current_index;

            self.current_index += 1;

            let entry_metadata = self.metadata[index];
            if !entry_metadata.is_empty() {
                return Some((entry_metadata, &self.data[index]));
            }
        }
    }
}

/// A trait that lets us abstract over different lengths of fixed size byte
/// arrays. Don't implement it for anything other than fixed size byte arrays!
pub trait ByteArray:
    Sized + Copy + Eq + Clone + PartialEq + Default + fmt::Debug + 'static
{
    fn as_slice(&self) -> &[u8];
    fn equals(&self, other: &Self) -> bool;
}

macro_rules! impl_byte_array {
    ($len:expr) => {
        impl ByteArray for [u8; $len] {
            #[inline(always)]
            fn as_slice(&self) -> &[u8] {
                &self[..]
            }

            // This custom implementation of comparing the fixed size arrays
            // seems make a big difference for performance (at least for
            // 16+ byte keys)
            #[inline]
            fn equals(&self, other: &Self) -> bool {
                // Most branches here are optimized away at compile time
                // because they depend on values known at compile time.

                let u64s = std::mem::size_of::<Self>() / 8;

                for i in 0..u64s {
                    let offset = i * 8;
                    let left = read_u64(&self[offset..offset + 8]);
                    let right = read_u64(&other[offset..offset + 8]);

                    if left != right {
                        return false;
                    }
                }

                return &self[u64s * 8..] == &other[u64s * 8..];

                #[inline]
                fn read_u64(bytes: &[u8]) -> u64 {
                    use std::convert::TryInto;
                    u64::from_le_bytes(bytes[..8].try_into().unwrap())
                }
            }
        }
    };
}

impl_byte_array!(0);
impl_byte_array!(1);
impl_byte_array!(2);
impl_byte_array!(3);
impl_byte_array!(4);
impl_byte_array!(5);
impl_byte_array!(6);
impl_byte_array!(7);
impl_byte_array!(8);
impl_byte_array!(9);
impl_byte_array!(10);
impl_byte_array!(11);
impl_byte_array!(12);
impl_byte_array!(13);
impl_byte_array!(14);
impl_byte_array!(15);
impl_byte_array!(16);
impl_byte_array!(17);
impl_byte_array!(18);
impl_byte_array!(19);
impl_byte_array!(20);
impl_byte_array!(21);
impl_byte_array!(22);
impl_byte_array!(23);
impl_byte_array!(24);
impl_byte_array!(25);
impl_byte_array!(26);
impl_byte_array!(27);
impl_byte_array!(28);
impl_byte_array!(29);
impl_byte_array!(30);
impl_byte_array!(31);
impl_byte_array!(32);

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use super::*;
    use crate::FxHashFn;

    fn make_table<
        I: Iterator<Item = (K, V)> + ExactSizeIterator,
        K: ByteArray,
        V: ByteArray,
        H: HashFn,
    >(
        xs: I,
    ) -> (Vec<EntryMetadata>, Vec<Entry<K, V>>) {
        let size = xs.size_hint().0.next_power_of_two();
        let mut data = vec![Entry::default(); size];
        let mut metadata = vec![EntryMetadata::default(); size];

        assert!(metadata.iter().all(EntryMetadata::is_empty));

        {
            let mut table: RawTableMut<K, V, H> = RawTableMut {
                metadata: &mut metadata[..],
                data: &mut data[..],
                mod_mask: size - 1,
                _hash_fn: Default::default(),
            };

            for (k, v) in xs {
                table.insert(k, v);
            }
        }

        (metadata, data)
    }

    // A hash function that extracts the first byte as hash value. This is
    // useful for handwritten tests because we can directly determine which
    // index a given key should end up at (i.e. its first byte).

    #[derive(Eq, PartialEq)]
    struct FirstByteHashFn;
    impl HashFn for FirstByteHashFn {
        fn hash(bytes: &[u8]) -> u32 {
            bytes[0] as u32
        }
    }

    macro_rules! mk {
        ($name:ident, $type:ident, [ $($entry:expr,)* ]) => {

            let mut metadata = Vec::new();
            let mut data = Vec::new();

            $({
                let entry = $entry;

                metadata.push(entry.0);
                data.push(entry.1);
            })*

            let mod_mask = data.len() - 1;
            let metadata = mk!($type, metadata);
            let data = mk!($type, data);

            #[allow(unused_mut)]
            let mut $name = $type {
                metadata,
                data,
                mod_mask,
                _hash_fn: PhantomData::<FirstByteHashFn>::default(),
            };
        };

        (RawTable, $x:expr) => { &$x };
        (RawTableMut, $x:expr) => { &mut $x };
    }

    fn entry<K: ByteArray, V: ByteArray>(hash: u32, key: K, value: V) -> (EntryMetadata, Entry<K, V>) {
        (EntryMetadata::occupied(hash | (1 << 31)), Entry::new(key, value))
    }

    fn empty_entry<K: ByteArray, V: ByteArray>() -> (EntryMetadata, Entry<K, V>) {
        (EntryMetadata::default(), Entry::default())
    }

    #[test]
    fn lookup_entry_in_desired_slot() {
        mk!(table, RawTable, [
            empty_entry(),
            entry(1, [1, 1], [1]),
            entry(2, [2, 1], [2]),
            empty_entry(),
        ]);

        assert_eq!(table.find(&[0, 0]), None);
        assert_eq!(table.find(&[1, 1]), Some(&[1]));
        assert_eq!(table.find(&[2, 1]), Some(&[2]));
        assert_eq!(table.find(&[3, 1]), None);
    }

    #[test]
    fn lookup_entry_that_needs_probing() {
        // The keys [1, 1], [1, 2], and [1, 3] all want the same slot in the
        // table. To reach the latter we have to do linear probing.
        mk!(table, RawTable, [
            empty_entry(),
            entry(1, [1, 1], [1]),
            entry(1, [1, 2], [2]),
            entry(1, [1, 3], [3]),
            empty_entry(),
            empty_entry(),
            empty_entry(),
            empty_entry(),
        ]);

        assert_eq!(table.find(&[1, 1]), Some(&[1]));
        assert_eq!(table.find(&[1, 2]), Some(&[2]));
        assert_eq!(table.find(&[1, 3]), Some(&[3]));
    }

    #[test]
    fn lookup_entry_that_needs_probing_with_wrapping() {
        // The keys [2, 1] and [2, 2] both want the same slot in the table.
        // [2, 2] has been moved one slot further (wrapping around to 0).
        mk!(table, RawTable, [
            entry(3, [3, 2], [1]),
            empty_entry(),
            empty_entry(),
            entry(3, [3, 1], [2]),
        ]);

        assert_eq!(table.find(&[3, 2]), Some(&[1]));
        assert_eq!(table.find(&[3, 1]), Some(&[2]));
    }

    #[test]
    fn insert_entry_at_desired_index() {
        mk!(table, RawTableMut, [
            empty_entry(),
            empty_entry(),
            empty_entry(),
            empty_entry(),
        ]);

        table.insert([1, 0], [1]);

        mk!(expected_table, RawTableMut, [
            empty_entry(),
            entry(1, [1, 0], [1]),
            empty_entry(),
            empty_entry(),
        ]);

        assert_eq!(table, expected_table);
    }

    #[test]
    fn insert_entry_one_past_desired_index() {
        mk!(table, RawTableMut, [
            empty_entry(),
            entry(1, [1, 0], [1]),
            empty_entry(),
            empty_entry(),
        ]);

        table.insert([1, 1], [2]);

        mk!(expected_table, RawTableMut, [
            empty_entry(),
            entry(1, [1, 0], [1]),
            entry(1, [1, 1], [2]),
            empty_entry(),
        ]);

        assert_eq!(table, expected_table);
    }

    #[test]
    fn insert_entry_that_pushes_down_other_entry() {
        mk!(table, RawTableMut, [
            empty_entry(),
            entry(1, [1, 0], [1]),
            entry(2, [2, 1], [2]),
            empty_entry(),
        ]);

        assert_eq!(table.insert([1, 1], [3]), None);

        mk!(expected_table, RawTableMut, [
                empty_entry(),
                entry(1, [1, 0], [1]),
                entry(1, [1, 1], [3]),
                entry(2, [2, 1], [2]),
            ]
        );

        assert_eq!(table, expected_table);
    }

    #[test]
    fn insert_entry_that_replaces_other_entry() {
        mk!(table, RawTableMut, [
            empty_entry(),
            entry(1, [1, 0], [1]),
            entry(2, [2, 1], [2]),
            empty_entry(),
        ]);

        assert_eq!(table.insert([1, 0], [3]), Some([1]));

        mk!(expected_table, RawTableMut, [
                empty_entry(),
                entry(1, [1, 0], [3]),
                entry(2, [2, 1], [2]),
                empty_entry(),
            ]
        );

        assert_eq!(table, expected_table);
    }

    #[test]
    fn insert_entry_that_replaces_other_entry_after_probing() {
        mk!(table, RawTableMut, [
            empty_entry(),
            entry(1, [1, 0], [1]),
            entry(1, [1, 1], [2]),
            empty_entry(),
        ]);

        assert_eq!(table.insert([1, 1], [3]), Some([2]));

        mk!(expected_table, RawTableMut, [
                empty_entry(),
                entry(1, [1, 0], [1]),
                entry(1, [1, 1], [3]),
                empty_entry(),
            ]
        );

        assert_eq!(table, expected_table);
    }

    #[test]
    fn stress() {
        let xs: Vec<[u8; 2]> = (0 ..= u16::MAX).map(|x| x.to_le_bytes()).collect();

        let (metadata, data) = make_table::<_, _, _, FxHashFn>(xs.iter().map(|x| (*x, *x)));

        let table: RawTable<_, _, FxHashFn> = RawTable {
            metadata: &metadata[..],
            data: &data[..],
            mod_mask: data.len() - 1,
            _hash_fn: PhantomData::default(),
        };

        for x in xs.iter() {
            assert_eq!(table.find(x), Some(x));
        }
    }
}
