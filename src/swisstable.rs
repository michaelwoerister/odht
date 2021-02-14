


use std::convert::TryInto;
use crate::HashFn;
use std::mem::size_of;
use std::marker::PhantomData;

type HashValue = u32;

const GROUP_SIZE: usize = 16;

const EMPTY_CONTROL_BYTE: u8 = 0b1000_0000;

pub(crate) struct SwissTable<'a, K: ByteArray, V: ByteArray, H: HashFn> {
    control: &'a [u8],
    data: &'a [Entry<K, V>],
    _hash_fn: PhantomData<H>,
}

#[inline]
fn h1(h: HashValue) -> usize {
    h as usize
}

#[inline]
fn h2(h: HashValue) -> u8 {
    const SHIFT: usize = size_of::<HashValue>() * 8 - 7;
    (h >> SHIFT) as u8
}

#[inline]
fn is_empty_or_deleted(control_byte: u8) -> bool {
    (control_byte & EMPTY_CONTROL_BYTE) != 0
}

#[cfg(not(any(
target_feature = "sse2",
any(target_arch = "x86", target_arch = "x86_64"),
not(miri)
)))]
mod group_query {
    use super::*;

    pub struct GroupQuery {
        matches: Vec<usize>,
        first_empty: Option<usize>,
    }

    impl GroupQuery {

        pub fn from(group: &[u8; 16], h2: u8) -> GroupQuery {
            debug_assert!(!is_empty_or_deleted(h2));

            let mut matches = Vec::new();
            let mut first_empty = None;

            for (i, &b) in group.iter().enumerate() {
                if b == h2 {
                    matches.push(i);
                }

                if (b & 0b1000_0000) != 0 && first_empty.is_none() {
                    first_empty = Some(i);
                }
            }

            GroupQuery {
                matches,
                first_empty,
            }
        }

        pub fn iter_matches(&self, mut f: impl FnMut(usize) -> bool) {
            for &m in &self.matches {
                if f(m) {
                    return
                }
            }
        }

        pub fn matches_iter(&self) -> MatchesIter {
            MatchesIter {
                group_query: self,
                index: 0,
            }
        }

        pub fn any_empty(&self) -> bool {
            self.first_empty.is_some()
        }

        pub fn first_empty(&self) -> Option<usize> {
            self.first_empty
        }
    }

    pub struct MatchesIter<'a> {
        group_query: &'a GroupQuery,
        index: usize,
    }

    impl<'a> Iterator for MatchesIter<'a> {
        type Item = usize;

        fn next(&mut self) -> Option<usize> {
            let i = self.index;
            self.index += 1;
            self.group_query.matches.get(i).cloned()
        }
    }
}


#[cfg(all(
target_feature = "sse2",
any(target_arch = "x86", target_arch = "x86_64"),
not(miri)
))]
mod group_query {
    #[cfg(target_arch = "x86")]
    use core::arch::x86;
    #[cfg(target_arch = "x86_64")]
    use core::arch::x86_64 as x86;

     pub struct GroupQuery {
        matches: u16,
        empty: u16,
    }

    impl GroupQuery {

        #[inline]
        pub fn from(group: &[u8; 16], h2: u8) -> GroupQuery {
            unsafe {
                let group = x86::_mm_loadu_si128(group as *const _ as *const x86::__m128i);
                let cmp_byte = x86::_mm_cmpeq_epi8(group, x86::_mm_set1_epi8(h2 as i8));
                let matches = x86::_mm_movemask_epi8(cmp_byte) as u16;
                let empty = x86::_mm_movemask_epi8(group) as u16;

                eprintln!("matches = {:b}", matches);
                eprintln!("empty = {:b}", empty);

                GroupQuery {
                    matches,
                    empty,
                }
            }
        }

        #[inline]
        pub fn matches_iter(&self) -> MatchesIter {
            MatchesIter {
                matches: self.matches,
            }
        }

        #[inline]
        pub fn any_empty(&self) -> bool {
            self.empty != 0
        }

        #[inline]
        pub fn first_empty(&self) -> Option<usize> {
            if self.empty == 0 {
                None
            } else {
                Some(self.empty.trailing_zeros() as usize)
            }
        }
    }

    pub struct MatchesIter {
        matches: u16,
    }

    impl Iterator for MatchesIter {
        type Item = usize;

        #[inline]
        fn next(&mut self) -> Option<usize> {
            if self.matches == 0 {
                None
            } else {
                let index = self.matches.trailing_zeros() as usize;
                self.matches &= !(1 << index);
                Some(index)
            }
        }
    }
}



type GroupQuery = group_query::GroupQuery;


struct PropeSeq {
    index: usize,
    stride: usize,
}

impl PropeSeq {
    #[inline]
    fn new(h1: usize, mask: usize) -> PropeSeq {
        PropeSeq {
            index: h1 & mask,
            stride: 0,
        }
    }

    #[inline]
    fn advance(&mut self, mask: usize) {
        self.stride += GROUP_SIZE;
        self.index += self.stride;
        self.index &= mask;
    }
}

#[inline]
fn group_starting_at(control_bytes: &[u8], index: usize) -> &[u8; GROUP_SIZE] {
    (&control_bytes[index .. index + GROUP_SIZE]).try_into().unwrap()
}

impl<'a, K: ByteArray, V: ByteArray, H: HashFn> SwissTable<'a, K, V, H> {

    #[inline]
    pub fn find(&self, key: &K) -> Option<&V> {
        debug_assert!(self.data.len().is_power_of_two());
        debug_assert!(self.control.len() == self.data.len() + GROUP_SIZE);

        let mask = self.data.len() - 1;
        let hash = H::hash(key.as_slice());
        let mut ps = PropeSeq::new(h1(hash), mask);
        let h2 = h2(hash);

        loop {
            let group_query = GroupQuery::from(
                group_starting_at(self.control, ps.index), h2);

            for m in group_query.matches_iter() {
                if self.data[ps.index + m].key == *key {
                    return Some(&self.data[ps.index + m].value);
                }
            }

            if group_query.any_empty() {
                return None;
            }

            ps.advance(mask);
        }
    }
}

pub(crate) fn new_empty_with_slot_count<K: ByteArray, V: ByteArray>(slot_count: usize) -> (Vec<u8>, Vec<Entry<K, V>>) {

    assert!(slot_count.is_power_of_two());
    assert!(slot_count % GROUP_SIZE == 0);

    let data = vec![Entry::default(); slot_count];
    let control = vec![0b1000_0000u8; slot_count + GROUP_SIZE];

    (control, data)
}

pub(crate) struct SwissTableMut<'a, K: ByteArray, V: ByteArray, H: HashFn> {
    control: &'a mut [u8],
    data: &'a mut [Entry<K, V>],
    _hash_fn: PhantomData<H>,
}

impl<'a, K: ByteArray, V: ByteArray, H: HashFn> SwissTableMut<'a, K, V, H> {

    #[inline]
    pub fn insert(&mut self, key: K, value: V) -> bool {
        debug_assert!(self.data.len().is_power_of_two());
        debug_assert!(self.control.len() == self.data.len() + GROUP_SIZE);

        let mask = self.data.len() - 1;
        let hash = H::hash(key.as_slice());

        let mut ps = PropeSeq::new(h1(hash), mask);
        let h2 = h2(hash);

        loop {
            let group_query = GroupQuery::from(
                group_starting_at(self.control, ps.index), h2);

            for m in group_query.matches_iter() {
                let entry = &mut self.data[ps.index + m];

                if entry.key == key {
                    entry.value = value;
                    return false
                }
            }

            if let Some(first_empty) = group_query.first_empty() {
                let index = ps.index + first_empty;
                self.data[index] = Entry { key, value };
                self.control[index] = h2;

                if index < GROUP_SIZE {
                    let first_mirror = self.data.len();
                    self.control[first_mirror + first_empty] = h2;
                }

                return true;
            }

            ps.advance(mask);
        }
    }
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


/// A trait that lets us abstract over different lengths of fixed size byte
/// arrays. Don't implement it for anything other than fixed size byte arrays!
pub trait ByteArray:
    Sized + Copy + Eq + Clone + PartialEq + Default + std::fmt::Debug + 'static
{
    fn as_slice(&self) -> &[u8];
}

macro_rules! impl_byte_array {
    ($len:expr) => {
        impl ByteArray for [u8; $len] {
            #[inline(always)]
            fn as_slice(&self) -> &[u8] {
                &self[..]
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
mod tests {
    use super::*;
    use crate::FxHashFn;

    #[test]
    fn stress() {

        let xs: Vec<[u8; 2]> = (0 .. 512u16).map(|x| x.to_le_bytes()).collect();

        let (mut control, mut data) = new_empty_with_slot_count(xs.len() * 2);

        for (i, &x) in xs.iter().enumerate() {
            let mut table: SwissTableMut<'_, _, _, FxHashFn> = SwissTableMut {
                control: &mut control,
                data: &mut data,
                _hash_fn: PhantomData::default(),
            };

            assert!(table.insert(x, x));

            for (j, &y) in xs.iter().enumerate() {
                let table: SwissTable<'_, _, _, FxHashFn> = SwissTable {
                    control: &table.control,
                    data: &table.data,
                    _hash_fn: PhantomData::default(),
                };

                if j <= i {
                    assert!(table.find(&y) == Some(&y));
                } else {
                    assert!(table.find(&y) == None);
                }

            }
        }
    }

    #[test]
    fn group_query_empty() {
        let control = [EMPTY_CONTROL_BYTE; GROUP_SIZE];
        let h2 = 0b0001_0101;

        let q = GroupQuery::from(&control, h2);

        assert_eq!(q.first_empty(), Some(0));
        assert_eq!(q.matches_iter().collect::<Vec<_>>(), vec![]);
    }

    #[test]
    fn group_query_one() {
        let mut control = [EMPTY_CONTROL_BYTE; GROUP_SIZE];
        let h2 = 0b0001_0101;

        control[3] = h2;

        let q = GroupQuery::from(&control, h2);

        assert_eq!(q.first_empty(), Some(0));
        assert_eq!(q.matches_iter().collect::<Vec<_>>(), vec![3]);
    }

    #[test]
    fn group_query_many() {
        let mut control = [EMPTY_CONTROL_BYTE; GROUP_SIZE];
        let h2 = 0b0001_0101;

        control[0] = h2;
        control[6] = h2;
        control[11] = h2;

        let q = GroupQuery::from(&control, h2);

        assert_eq!(q.first_empty(), Some(1));
        assert_eq!(q.matches_iter().collect::<Vec<_>>(), vec![0, 6, 11]);
    }

    #[test]
    fn group_query_all_full() {
        let control = [123u8; GROUP_SIZE];
        let h2 = 56u8;

        let q = GroupQuery::from(&control, h2);

        assert_eq!(q.first_empty(), None);
        assert_eq!(q.matches_iter().collect::<Vec<_>>(), vec![]);
    }
}
