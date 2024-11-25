use std::fs::File;
use std::io;
use std::io::Write;
use std::ops::Range;
use memmap2::Mmap;

use tempfile::NamedTempFile;


#[derive(Debug, Clone)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
    pub file_name: String,
    pub parent: Option<Box<Pos>>,
}

impl Pos {
    pub(crate) fn clone(&self) -> Pos {
        Pos {
            line: self.line,
            col: self.col,
            file_name: self.file_name.clone(),
            parent: match &self.parent {
                Some(p) => Some(Box::from((*p).clone())),
                None => None,
            },
        }
    }
}

pub struct Input {
    pub(crate) pos: Pos,
    mmap: Mmap,
    index: usize,
    current_char_len: Option<usize>,
    current_char: Option<char>,
    eof: bool,
}

impl Input {
    /// Creates a new `MmapCharReader` from the specified file path.
    pub fn new(file_path: &str) -> io::Result<Input> {
        // Open the file
        let file = File::open(file_path)?;

        // Create a memory map
        let mmap = unsafe { Mmap::map(&file)? };

        // Create a `Chars` iterator from the string slice
        Ok(Input {
            pos: Pos {
                line: 1,
                col: 1,
                file_name: file_path.to_string(),
                parent: None,
            },
            mmap,
            index: 0,
            current_char_len: None,
            current_char: None,
            eof: false,
        })
    }

    pub fn peek_char(&mut self) -> Result<Option<char>, String> {
        let c = first_utf8_char(&self.mmap[self.index..]);
        match c {
            Ok(Some((c, len))) => {
                self.current_char_len = Some(len);
                self.current_char = Some(c);
                Ok(Some(c))
            }
            Ok(None) => {
                self.current_char_len = None;
                self.current_char = None;
                self.eof = true;
                Ok(None)
            }
            Err(c) => Err(c.to_string()),
        }
    }

    pub fn step(&mut self) {
        match (self.current_char_len, self.current_char) {
            (Some(len), Some(c)) => {
                self.index += len;
                if c == '\n' {
                    self.pos.line += 1;
                    self.pos.col = 1;
                } else {
                    self.pos.col += 1;
                }
                self.current_char_len = None;
                self.current_char = None;
            }
            (None, _) | (_, None) => {
                panic!("{}", if self.eof { "Stepping over eof" } else { "step called without peek_char" });
            }
        }
    }

    pub fn len(&self) -> usize {
        self.mmap.len()
    }

    // Reads ahead 'len' characters and returns them as a string
    // After reading ahead, but before returning it sets the index back to the original value.
    // The length of the returned string may be less than 'len' if EOF is reached.
    pub fn read(&mut self, len: usize) -> String {
        let start = self.current_byte_index();
        let mut i = 0;
        let mut result = String::new();
        while i < len {
            if let Ok(Some(ch)) = self.peek_char() {
                result.push(ch);
                self.step();
            }
            i = i + 1;
        }
        self.reset(start);
        result
    }

    // Get the byte slice from the mmap and return it as a string
    pub fn slice(&self, range: Range<usize>) -> String {
        std::str::from_utf8(&self.mmap[range]).unwrap().to_string()
    }

    pub fn reset(&mut self, index: usize) {
        self.index = index;
    }

    pub fn current_byte_index(&self) -> usize {
        self.index
    }
}

fn first_utf8_char(bytes: &[u8]) -> Result<Option<(char, usize)>, &str> {
    if bytes.is_empty() {
        return Ok(None);
    }

    let first_byte = bytes[0];

    // Determine the number of bytes in the UTF-8 character based on the first byte
    let char_len = match first_byte {
        0x00..=0x7F => 1,           // 1-byte character (ASCII)
        0xC0..=0xDF => 2,           // 2-byte character
        0xE0..=0xEF => 3,           // 3-byte character
        0xF0..=0xF7 => 4,           // 4-byte character
        _ => return Err("Invalid UTF-8 starting byte"),           // Invalid UTF-8 starting byte
    };

    // Ensure we have enough bytes in the array for the character
    if bytes.len() < char_len {
        return Err("Not enough bytes for character");
    }

    // Attempt to decode the character from the valid UTF-8 slice
    match std::str::from_utf8(&bytes[..char_len]) {
        Ok(s) => Ok(s.chars().next().map(|c| (c, char_len))), // Return the character and its byte length
        Err(_) => Err("Invalid UTF-8 character"), // Invalid UTF-8 character
    }
}

#[cfg(test)]
impl Input {
    pub fn from_string(content: &str) -> io::Result<Input> {
        // Create a temporary file
        let mut temp_file = NamedTempFile::new()?;

        temp_file.write(&content.as_bytes())?;

        // Get the path of the temporary file and call `new` method
        let file_path = temp_file.path().to_str().unwrap().to_string();

        // Create the Input struct using the new method and return it
        Input::new(&file_path)
    }
}