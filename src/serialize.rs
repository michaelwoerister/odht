use crate::error::Error;
use crate::raw_table::RawTable;
use crate::raw_table::{Entry, EntryMetadata};
use crate::Config;
use std::{
    convert::TryInto,
    mem::{align_of, size_of},
};

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct Header {
    tag: [u8; 4],
    size_of_metadata: u8,
    size_of_key: u8,
    size_of_value: u8,
    size_of_header: u8,

    max_load_factor_percent: u8,

    item_count: [u8; 8],
    slot_count: [u8; 8],

    // Let's keep things at least 8 byte aligned
    padding: [u8; 7],
}

const HEADER_TAG: [u8; 4] = *b"ODHT";
const HEADER_SIZE: usize = size_of::<Header>();

impl Header {
    pub fn new<C: Config>(
        item_count: usize,
        slot_count: usize,
        max_load_factor_percent: u8,
    ) -> Header {
        assert!(HEADER_SIZE % 8 == 0);

        Header {
            tag: HEADER_TAG,
            size_of_metadata: size_of::<EntryMetadata>().try_into().unwrap(),
            size_of_key: size_of::<C::RawKey>().try_into().unwrap(),
            size_of_value: size_of::<C::RawValue>().try_into().unwrap(),
            size_of_header: size_of::<Header>().try_into().unwrap(),
            max_load_factor_percent: max_load_factor_percent.try_into().unwrap(),
            padding: [0u8; 7],
            item_count: (item_count as u64).to_le_bytes(),
            slot_count: (slot_count as u64).to_le_bytes(),
        }
    }

    pub fn item_count(&self) -> usize {
        u64::from_le_bytes(self.item_count) as usize
    }

    pub fn slot_count(&self) -> usize {
        u64::from_le_bytes(self.slot_count) as usize
    }

    pub fn mod_mask(&self) -> usize {
        assert!(self.slot_count().is_power_of_two());
        self.slot_count() - 1
    }

    pub fn max_load_factor_percent(&self) -> u8 {
        self.max_load_factor_percent
    }

    fn metadata_offset(&self) -> isize {
        HEADER_SIZE as isize
    }

    fn data_offset(&self) -> isize {
        (HEADER_SIZE + self.slot_count() * size_of::<EntryMetadata>()) as isize
    }

    fn serialize(&self, w: &mut dyn std::io::Write) -> Result<(), Box<dyn std::error::Error>> {
        let bytes =
            unsafe { std::slice::from_raw_parts(self as *const _ as *const u8, HEADER_SIZE) };

        Ok(w.write_all(bytes)?)
    }

    fn from_serialized<'a, C: Config>(data: &'a [u8]) -> Result<&'a Header, Error> {
        if data.len() < HEADER_SIZE {
            return Err(Error(format!("Provided data not big enough for header.")));
        }

        let header: &'a Header = unsafe { &*(data.as_ptr() as *const Header) };

        if header.tag != HEADER_TAG {
            return Err(Error(format!(
                "Expected header tag {:?} but found {:?}",
                HEADER_TAG, header.tag
            )));
        }

        check_expected_size::<EntryMetadata>(header.size_of_metadata)?;
        check_expected_size::<C::RawKey>(header.size_of_key)?;
        check_expected_size::<C::RawValue>(header.size_of_value)?;
        check_expected_size::<Header>(header.size_of_header)?;

        let bytes_per_entry =
            size_of::<Entry<C::RawKey, C::RawValue>>() + size_of::<EntryMetadata>();

        if data.len() < HEADER_SIZE + header.slot_count() * bytes_per_entry {
            return Err(Error(format!(
                "Provided data not big enough for slot count {}",
                header.slot_count()
            )));
        }

        if !header.slot_count().is_power_of_two() {
            return Err(Error(format!(
                "Slot count of hashtable should be a power of two but is {}",
                header.slot_count()
            )));
        }

        return Ok(header);

        fn check_expected_size<T>(expected_size: u8) -> Result<(), Error> {
            if expected_size as usize != size_of::<T>() {
                Err(Error(format!(
                    "Expected size of Config::RawValue to be {} but the encoded \
                     table specifies {}. This indicates an encoding mismatch.",
                    size_of::<T>(),
                    expected_size
                )))
            } else {
                Ok(())
            }
        }
    }
}

pub(crate) fn serialize<C: Config>(
    metadata: &[EntryMetadata],
    entry_data: &[Entry<C::RawKey, C::RawValue>],
    item_count: usize,
    max_load_factor_percent: u8,
    w: &mut dyn std::io::Write,
) -> Result<(), Box<dyn std::error::Error>> {
    assert!(metadata.len().is_power_of_two());
    assert!(metadata.len() == entry_data.len());

    let header = Header::new::<C>(item_count, metadata.len(), max_load_factor_percent);

    header.serialize(w)?;

    w.write_all(as_byte_slice(metadata))?;
    w.write_all(as_byte_slice(entry_data))?;

    Ok(())
}

pub(crate) fn deserialize<C: Config>(
    data: &[u8],
) -> Result<(&Header, &[EntryMetadata], &[Entry<C::RawKey, C::RawValue>]), Box<dyn std::error::Error>>
{
    assert!(align_of::<Entry<C::RawKey, C::RawValue>>() == 1);
    assert!(align_of::<EntryMetadata>() == 1);

    let header = Header::from_serialized::<C>(data)?;

    let raw_metadata: &[EntryMetadata] = unsafe {
        std::slice::from_raw_parts(
            data.as_ptr().offset(header.metadata_offset()) as *const EntryMetadata,
            header.slot_count(),
        )
    };

    let raw_data: &[Entry<C::RawKey, C::RawValue>] = unsafe {
        std::slice::from_raw_parts(
            data.as_ptr().offset(header.data_offset()) as *const Entry<C::RawKey, C::RawValue>,
            header.slot_count(),
        )
    };

    let raw_table = RawTable::<'_, C::RawKey, C::RawValue, C::H>::new(
        raw_metadata,
        raw_data,
        header.mod_mask(),
    );
    raw_table.sanity_check_hashes(3)?;

    Ok((header, raw_metadata, raw_data))
}

fn as_byte_slice<T>(slice: &[T]) -> &[u8] {
    assert!(slice.len().is_power_of_two());
    assert!(align_of::<T>() == 1);
    let byte_ptr = slice.as_ptr() as *const u8;
    let num_bytes = slice.len() * size_of::<T>();

    unsafe { std::slice::from_raw_parts(byte_ptr, num_bytes) }
}

pub(crate) fn bytes_needed<C: Config>(capacity: usize) -> usize {
    let bytes_per_entry = size_of::<EntryMetadata>() + size_of::<Entry<C::RawKey, C::RawValue>>();
    HEADER_SIZE + bytes_per_entry * capacity
}