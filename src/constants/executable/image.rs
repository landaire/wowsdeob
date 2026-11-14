//! Enough of the PE32+ format to follow pointers stored in the client
//! executable's data sections back to the strings they name.

use std::collections::BTreeSet;

use memchr::memmem;

/// `IMAGE_SCN_MEM_EXECUTE`.
const EXECUTABLE_SECTION: u32 = 0x2000_0000;
/// The optional header magic of a 64-bit image.
const PE32_PLUS_MAGIC: u16 = 0x20b;
/// The module every CPython build lists in its built-in module table.
const ANCHOR_MODULE: &[u8] = b"marshal";

/// A virtual address in the loaded image.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct VirtualAddress(u64);

struct Section {
    start: VirtualAddress,
    raw_offset: usize,
    raw_size: usize,
    executable: bool,
}

impl Section {
    fn file_offset(&self, address: VirtualAddress) -> Option<usize> {
        let delta = usize::try_from(address.0.checked_sub(self.start.0)?).ok()?;

        (delta < self.raw_size).then_some(self.raw_offset + delta)
    }

    fn address(&self, offset: usize) -> Option<VirtualAddress> {
        let delta = offset.checked_sub(self.raw_offset)?;
        if delta >= self.raw_size {
            return None;
        }

        self.start.0.checked_add(u64::try_from(delta).ok()?).map(VirtualAddress)
    }
}

pub struct Image<'a> {
    bytes: &'a [u8],
    sections: Vec<Section>,
}

impl<'a> Image<'a> {
    /// `None` when `bytes` is not a PE32+ image.
    pub fn parse(bytes: &'a [u8]) -> Option<Self> {
        let header = usize::try_from(read_u32(bytes, 0x3c)?).ok()?;
        if bytes.get(header..header + 4)? != b"PE\0\0" {
            return None;
        }

        let section_count = usize::from(read_u16(bytes, header + 6)?);
        let optional_size = usize::from(read_u16(bytes, header + 20)?);
        let optional = header + 24;
        if read_u16(bytes, optional)? != PE32_PLUS_MAGIC {
            return None;
        }
        let image_base = read_u64(bytes, optional + 24)?;

        let mut sections = Vec::with_capacity(section_count);
        for index in 0..section_count {
            let entry = optional + optional_size + 40 * index;
            let relative = read_u32(bytes, entry + 12)?;
            let raw_size = usize::try_from(read_u32(bytes, entry + 16)?).ok()?;
            let raw_offset = usize::try_from(read_u32(bytes, entry + 20)?).ok()?;
            let characteristics = read_u32(bytes, entry + 36)?;
            sections.push(Section {
                start: VirtualAddress(image_base.checked_add(u64::from(relative))?),
                raw_offset,
                raw_size,
                executable: characteristics & EXECUTABLE_SECTION != 0,
            });
        }

        Some(Self { bytes, sections })
    }

    /// The names in CPython's static built-in module table, an array of
    /// (name pointer, init function pointer) pairs ending in a null pair.
    /// It is found from a pointer to `marshal`'s name.
    pub fn builtin_module_table(&self) -> Option<BTreeSet<String>> {
        let mut anchor_text = Vec::with_capacity(ANCHOR_MODULE.len() + 2);
        anchor_text.push(0);
        anchor_text.extend_from_slice(ANCHOR_MODULE);
        anchor_text.push(0);
        let anchor_offset = memmem::find(self.bytes, &anchor_text)? + 1;
        let anchor = self.address_of(anchor_offset)?;

        let entry = memmem::find_iter(self.bytes, &anchor.0.to_le_bytes())
            .find(|offset| self.table_entry(*offset).is_some())?;

        let mut first = entry;
        while let Some(previous) = first.checked_sub(16).filter(|offset| self.table_entry(*offset).is_some()) {
            first = previous;
        }

        let mut names = BTreeSet::new();
        let mut cursor = first;
        while let Some(name) = self.table_entry(cursor) {
            names.insert(name);
            cursor += 16;
        }

        // The table must end in a null pair.
        (read_u64(self.bytes, cursor)? == 0 && read_u64(self.bytes, cursor + 8)? == 0).then_some(names)
    }

    /// The module name of a table entry at `offset`: a pointer to an
    /// identifier-like string followed by a pointer into code, or by null
    /// for the modules the runtime creates itself (`sys`, `__builtin__`).
    fn table_entry(&self, offset: usize) -> Option<String> {
        let name = VirtualAddress(read_u64(self.bytes, offset)?);
        let init = VirtualAddress(read_u64(self.bytes, offset + 8)?);
        let init_in_code =
            self.sections.iter().any(|section| section.executable && section.file_offset(init).is_some());
        if init.0 != 0 && !init_in_code {
            return None;
        }

        let start = self.offset_of(name)?;
        let length = self.bytes.get(start..)?.iter().take(64).position(|byte| *byte == 0)?;
        let text = self.bytes.get(start..start + length)?;
        let identifier =
            !text.is_empty() && text.iter().all(|byte| byte.is_ascii_alphanumeric() || *byte == b'_' || *byte == b'.');

        identifier.then(|| String::from_utf8_lossy(text).into_owned())
    }

    fn offset_of(&self, address: VirtualAddress) -> Option<usize> {
        self.sections.iter().find_map(|section| section.file_offset(address))
    }

    fn address_of(&self, offset: usize) -> Option<VirtualAddress> {
        self.sections.iter().find_map(|section| section.address(offset))
    }
}

fn read_u16(bytes: &[u8], offset: usize) -> Option<u16> {
    Some(u16::from_le_bytes(bytes.get(offset..offset + 2)?.try_into().ok()?))
}

fn read_u32(bytes: &[u8], offset: usize) -> Option<u32> {
    Some(u32::from_le_bytes(bytes.get(offset..offset + 4)?.try_into().ok()?))
}

fn read_u64(bytes: &[u8], offset: usize) -> Option<u64> {
    Some(u64::from_le_bytes(bytes.get(offset..offset + 8)?.try_into().ok()?))
}
