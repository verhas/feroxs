use std::collections::HashSet;
use input::{Input, Pos};
use crate::input;

#[derive(Debug, PartialEq, Eq)]
pub enum LexemeType {
    DoubleQuotedString,
    TripleDoubleQuotedString,
    SingleQuotedString,
    TripleSingleQuotedString,
    HereString,
    IntegerLiteral,
    FloatLiteral,
    Identifier,
    Keyword,
    Operator,
    Whitespace,
    Newline,
    SingleCharacter,
}

#[derive(Debug)]
pub enum LexemeValue {
    Integer(i64),
    Float(f64),
    String(String),
    // Add other types as needed
}

#[derive(Debug)]
pub struct Lexeme {
    pub token_type: LexemeType,
    pub value: Option<LexemeValue>,
    pub lex: String,
    pub pos: Pos,
}

pub struct LexerConfig {
    pub(crate) skip_whitespace: bool,
    pub(crate) treat_newline_as_whitespace: bool,
}

pub struct Lexer {
    input: Input,
    keywords: HashSet<&'static str>,
    operators: Vec<&'static str>,
    config: LexerConfig,
}

#[derive(Debug)]
pub struct LexerError {
    pub message: String,
    pub pos: Pos,
}

type LexerResult<'k> = Result<Lexeme, LexerError>;

pub struct Position {
    pub index: usize,
}

impl Lexer {
    pub fn new(
        input: Input,
        keywords: HashSet<&'static str>,
        operators: Vec<&'static str>,
        config: LexerConfig,
    ) -> Self {
        Lexer {
            input,
            keywords,
            operators,
            config,
        }
    }

    fn err(&self, message: &str) -> LexerResult {
        Err(LexerError {
            message: message.to_string(),
            pos: self.input.pos.clone(),
        })
    }

    pub fn get_position(&self) -> Position {
        Position {
            index: self.input.current_byte_index(),
        }
    }

    pub fn set_position(&mut self, pos: Position) {
        self.input.reset(pos.index);
    }

    /// Reads a single line of text from the `Lexer` input stream until a newline character (`'\n'`)
    /// or the end of the input is reached. This method collects all characters from the input stream
    /// directly, without processing or trimming, until it encounters a newline or the end of the file.
    /// If there is any line-feed (`'\r'`) character in the line, it is ignored.
    ///
    /// ### Returns
    ///
    /// - `Ok(Some(&str))` - A slice of the accumulated line as a `&str` if characters were successfully
    ///   read up to a newline or the end of input. The line terminating new-line is not included in the
    ///   returned slice.
    /// - `Ok(None)` - If the end of input is reached without reading any characters.
    /// - `Err(&str)` - If an error occurs while accessing characters from the input.
    ///
    /// ### Errors
    ///
    /// Returns an error `&str` if an issue arises when peeking or advancing through the input stream.
    /// It uses the `peek_char()` and `step()` methods of the `Input` struct to access each character.
    ///
    /// ### Example
    ///
    /// ```rust
    /// let mut lexer = Lexer::new(input, keywords, operators, config);
    /// match lexer.line_direct() {
    ///     Ok(Some(line)) => println!("Read line: {}", line),
    ///     Ok(None) => println!("Reached end of input"),
    ///     Err(e) => eprintln!("Error reading line: {}", e),
    /// }
    /// ```
    pub fn line_direct(&mut self) -> Result<Option<&str>, &str> {
        if let Ok(None) = self.input.peek_char() {
            return Ok(None);
        }
        let mut line = String::new();
        loop {
            match self.input.peek_char() {
                Ok(Some(ch)) => {
                    self.input.step();
                    if ch == '\r' {
                        continue;
                    }
                    if ch == '\n' {
                        break;
                    }
                    line.push(ch);
                }
                Ok(None) => {
                    break;
                }
                Err(e) => {
                    return Err(e);
                }
            }
        }
        Ok(Some(line.as_str()))
    }

    /// Fetches the next lexeme from the input.
    pub fn next_lexeme(&mut self) -> Option<LexerResult> {
        loop {
            let c = self.input.peek_char();
            match c {
                Ok(Some(ch)) => {
                    if ch == '\n' {
                        if self.config.treat_newline_as_whitespace {
                            if self.config.skip_whitespace {
                                self.input.step();
                                continue;
                            } else {
                                return Some(self.parse_whitespace());
                            }
                        } else {
                            return Some(self.parse_newline());
                        }
                    } else if ch.is_whitespace() {
                        if self.config.skip_whitespace {
                            self.input.step();
                            continue;
                        } else {
                            return Some(self.parse_whitespace());
                        }
                    }
                    if ch.is_alphabetic() || ch == '_' || ch == '$' {
                        return Some(self.parse_identifier_or_keyword());
                    }
                    if ch.is_digit(10) || ch == '.' || ch == '+' || ch == '-' {
                        if let Some(lexeme) = self.parse_number_literal() {
                            return Some(Ok(lexeme));
                        }
                    }
                    if ch == '"' {
                        return Some(self.parse_string_literal());
                    }
                    if ch == '\'' {
                        return Some(self.parse_single_quoted_string());
                    }

                    if ch == '<' {
                        match self.parse_here_string() {
                            Some(Ok(lexeme)) => { return Some(Ok(lexeme)) }
                            Some(Err(e)) => { return Some(Err(e)) }
                            None => {}
                        }
                    }
                    return Some(self.parse_operator());
                }
                Ok(None) => {
                    return None;
                }
                Err(e) => {
                    let error_message = e.to_string();
                    return Some(self.err(&error_message));
                }
            };
        }
    }

    /// Parses identifiers and keywords.
    fn parse_identifier_or_keyword(&mut self) -> LexerResult {
        let start = self.input.current_byte_index();
        while let Ok(Some(ch)) = self.input.peek_char() {
            if ch.is_alphanumeric() || ch == '_' || ch == '$' {
                self.input.step();
            } else {
                break;
            }
        }
        let end = self.input.current_byte_index();
        let slice = self.input.slice(start..end);
        let token_type = if self.keywords.contains(slice.as_str()) {
            LexemeType::Keyword
        } else {
            LexemeType::Identifier
        };
        Ok(Lexeme {
            token_type,
            value: None,
            lex: slice,
            pos: self.input.pos.clone(),
        })
    }

    /// Parses a number literal from the input stream, handling hexadecimal, octal, decimal, and
    /// floating-point formats. Returns an `Option<Lexeme>` containing the parsed number or `None`
    /// if parsing fails.
    ///
    /// ### Supported Formats
    /// - **Hexadecimal** (prefix `0x`): Parses hexadecimal numbers using digits `0-9` and `a-f`/`A-F`.
    /// - **Octal** (prefix `0o`): Parses octal numbers using digits `0-7`.
    /// - **Decimal**: Parses standard base-10 integers, allowing optional fractional parts for floats.
    /// - **Floating-point**: Identified by a decimal point (e.g., `3.14`). If a number has multiple
    ///   decimal points, it is invalid, and parsing fails.
    ///
    /// ### Returns
    /// - `Some(Lexeme)` if a valid number is parsed, with `Lexeme` containing:
    ///     - `LexemeType::NumberLiteral` as the token type.
    ///     - A `LexemeValue` of either `Integer` or `Float`, depending on whether the number
    ///       is integral or floating-point.
    ///     - The string slice representing the parsed number in the input.
    ///     - The position in the input where the lexeme was found.
    /// - `None` if parsing fails or the input does not conform to any valid number format.
    ///
    /// ### Example
    /// ```rust
    /// let input = "0x1A"; // Parses as hexadecimal, returning `Some(LexemeValue::Integer(26))`.
    /// let input = "0o17"; // Parses as octal, returning `Some(LexemeValue::Integer(15))`.
    /// let input = "123.45"; // Parses as float, returning `Some(LexemeValue::Float(123.45))`.
    /// ```
    ///
    /// ### Implementation Details
    /// - **Hexadecimal**: After detecting the prefix `0x`, it iterates through characters in the
    ///   hexadecimal range (`0-9`, `a-f`/`A-F`) and converts them to an integer using base-16.
    /// - **Octal**: Detects prefix `0o` and parses digits `0-7`, converting them to an integer
    ///   using base-8.
    /// - **Decimal/Floating-point**: Parses decimal digits and allows a single decimal point.
    ///   If a decimal point is found, the number is flagged as a float and parsed as `f64`.
    ///
    /// The method resets the input state if an invalid character is encountered, ensuring
    /// parsing robustness for future attempts.
    fn parse_number_literal(&mut self) -> Option<Lexeme> {
        let start = self.input.current_byte_index();
        let mut is_float = false;

        if let Ok(Some('0')) = self.input.peek_char() {
            self.input.step();
            if let Ok(Some(ch @ 'x') | Some(ch @ 'o') | Some(ch @ 'b')) = self.input.peek_char() {
                let radix = match ch {
                    'x' => 16,
                    'o' => 8,
                    'b' => 2,
                    _ => panic!("Invalid radix character"),
                };
                self.input.step();
                // Parse hexadecimal digits
                while let Ok(Some(ch)) = self.input.peek_char() {
                    if ch.is_digit(radix) {
                        self.input.step();
                    } else {
                        break;
                    }
                }
                let end = self.input.current_byte_index();
                let slice = self.input.slice(start..end);
                return if let Ok(value) = i64::from_str_radix(&slice[2..], radix) {
                    Some(Lexeme {
                        token_type: LexemeType::IntegerLiteral,
                        value: Some(LexemeValue::Integer(value)),
                        lex: slice,
                        pos: self.input.pos.clone(),
                    })
                } else {
                    // famous last words
                    panic!("Failed to parse integer from slice: {} after it was checked. Should not happen.", slice);
                };
            }
        }
        // Parse decimal numbers
        while let Ok(Some(ch)) = self.input.peek_char() {
            if ch.is_digit(10) {
                self.input.step();
            } else if ch == '.' {
                if is_float {
                    // Multiple decimal points are invalid, it stops the parsing
                    break;
                }
                is_float = true;
                self.input.step();
            } else if ch == 'e' || ch == 'E' {
                is_float = true;
                self.input.step();
                if let Ok(Some('+') | Some('-')) = self.input.peek_char() {
                    self.input.step();
                }
                while let Ok(Some(ch)) = self.input.peek_char() {
                    if ch.is_digit(10) {
                        self.input.step();
                    } else {
                        break;
                    }
                }
            } else {
                break;
            }
        }
        let end = self.input.current_byte_index();
        let slice = self.input.slice(start..end);
        if is_float {
            if let Ok(value) = slice.parse::<f64>() {
                return Some(Lexeme {
                    token_type: LexemeType::FloatLiteral,
                    value: Some(LexemeValue::Float(value)),
                    lex: slice,
                    pos: self.input.pos.clone(),
                });
            } else {
                // famous last words
                panic!("Failed to parse float from slice: {} after it was checked. Should not happen.", slice);
            }
        } else {
            if let Ok(value) = slice.parse::<i64>() {
                Some(Lexeme {
                    token_type: LexemeType::IntegerLiteral,
                    value: Some(LexemeValue::Integer(value)),
                    lex: slice,
                    pos: self.input.pos.clone(),
                })
            } else {
                self.input.reset(start);
                None
            }
        }
    }

    fn check_triple(&mut self, ch: char) -> bool {
        let first_char_index = self.input.current_byte_index();

        if let Ok(Some(c1)) = self.input.peek_char() {
            if c1 == ch {
                self.input.step();
                if let Ok(Some(c2)) = self.input.peek_char() {
                    if c2 == ch {
                        self.input.step();
                        true
                    } else {
                        self.input.reset(first_char_index);
                        false
                    }
                } else {
                    self.input.reset(first_char_index);
                    false
                }
            } else {
                self.input.reset(first_char_index);
                false
            }
        } else {
            self.input.reset(first_char_index);
            false
        }
    }


    /// Parses double-quoted string literals with escape sequences.
    fn parse_string_literal(&mut self) -> LexerResult {
        let start = self.input.current_byte_index();
        self.input.step(); // Consume the opening quote
        let triple = self.check_triple('"');

        let mut string_collected = String::new();
        let mut escaped = false;

        while let Ok(Some(ch)) = self.input.peek_char() {
            self.input.step();
            if escaped {
                escaped = false;
                string_collected.push(ch);
            } else if ch == '\\' {
                escaped = true;
                string_collected.push(ch);
            } else if !escaped && ch == '"' {
                if triple {
                    if !self.check_triple('"') {
                        string_collected.push('"');
                        continue;
                    }
                }
                // End of string
                let end = self.input.current_byte_index();
                let slice = self.input.slice(start..end);
                let escaped_string = match self.process_escapes(&string_collected) {
                    Ok(processed_line) => processed_line,
                    Err(e) => return self.err(e),
                };
                return Ok(Lexeme {
                    token_type: if triple { LexemeType::TripleDoubleQuotedString } else { LexemeType::DoubleQuotedString },
                    value: Some(LexemeValue::String(escaped_string)),
                    lex: slice,
                    pos: self.input.pos.clone(),
                });
            } else {
                string_collected.push(ch);
            }
        }

        // If we reach here, the string was not properly terminated
        // Handle error (e.g., return an error lexeme or report an error)
        self.err("unterminated string")
    }


    /// Parses single-quoted string literals without escape sequences.
    fn parse_single_quoted_string(&mut self) -> LexerResult {
        let mut processed_string = String::new();

        let start = self.input.current_byte_index();
        let triple = self.check_triple('\'');

        self.input.peek_char().expect("Error peeking char, which was already peeked");
        self.input.step(); // Consume the opening quote

        while let Ok(Some(ch)) = self.input.peek_char() {
            self.input.step();

            if ch == '\n' && !triple {
                return self.err("unexpected newline in single-quoted string");
            }
            if ch == '\r' {
                continue;
            }
            if ch == '\'' {
                if triple {
                    if !self.check_triple('\'') {
                        processed_string.push('\'');
                        continue;
                    }
                }
                break;
            }
            processed_string.push(ch);
        }
        let end = self.input.current_byte_index();
        let slice = self.input.slice(start..end);

        Ok(Lexeme {
            token_type: if triple { LexemeType::TripleSingleQuotedString } else { LexemeType::SingleQuotedString },
            value: Some(LexemeValue::String(processed_string)),
            lex: slice,
            pos: self.input.pos.clone(),
        })
    }

    fn parse_here_string(&mut self) -> Option<LexerResult> {
        let start_pos = self.input.pos.clone();
        let start = self.input.current_byte_index();
        self.input.step(); // Consume the first '<'
        if let Ok(Some('<')) = self.input.peek_char() {
            self.input.step(); // consume the second '<'
        } else {
            // there was no second '<' after the first
            self.input.reset(start);
            return None;
        }

        // Determine if it's a parsed or non-parsed here doc
        let quote_char = match self.input.peek_char() {
            Ok(Some(ch @ '\'')) | Ok(Some(ch @ '"')) => {
                self.input.step(); // Consume the quote character
                ch
            }
            Ok(Some(ch)) if ch.is_whitespace() => {
                // there is a space after the <<, this is not a here-doc
                self.input.reset(start);
                return None;
            }
            Ok(None) => {
                // the file ends after the <<, this is not a here-doc
                self.input.reset(start);
                return None;
            }
            _ => {
                '\n'
            }
        };

        // Read the delimiter
        let delimiter_start = self.input.current_byte_index();
        while let Ok(Some(ch)) = self.input.peek_char() {
            if ch == '\r' {
                self.input.step();
                continue;
            }
            if ch == quote_char {
                break;
            }
            if ch == '\n' {
                return Some(self.err("unexpected newline in delimiter"));
            }
            self.input.step();
        }
        if let Ok(None) = self.input.peek_char() {
            // Reached the end of input without finding the closing quote, not a here-string
            // like <<"here we go... <- and then end of the file
            return Some(self.err("unexpected eof in delimiter"));
        }
        let delimiter_end = self.input.current_byte_index();
        let delimiter = self.input.slice(delimiter_start..delimiter_end);
        self.input.step();

        if quote_char != '\n' {
            // when the delimiter was quoted, then there can be some space after the delimiter
            while let Ok(Some(ch)) = self.input.peek_char() {
                self.input.step();
                if ch == '\n' {
                    break;
                }
                // There can be some space after the <<"END" .... \n <- before the new line
                // also explicitly ignore \r for the sake of Windows
                if !ch.is_whitespace() && ch != '\r' {
                    return Some(self.err("unexpected character after delimiter"));
                }
            }
        }

        if let Ok(None) = self.input.peek_char() {
            return Some(self.err("unexpected eof while parsing here doc"));
        }

        // Read content lines until we find the delimiter line
        let mut content = String::new();
        loop {
            let line_start = self.input.current_byte_index();
            let mut line_end = line_start;
            let mut is_end_of_line = false;

            while let Ok(Some(ch)) = self.input.peek_char() {
                self.input.step();
                line_end = self.input.current_byte_index();
                if ch == '\n' {
                    is_end_of_line = true;
                    break;
                }
            }

            let line = &self.input.slice(line_start..if is_end_of_line { line_end - 1 } else { line_end });

            if line.trim_end() == delimiter {
                break;
            } else {
                if !content.is_empty() {
                    content.push('\n');
                }
                if quote_char == '"' {
                    // Parsed here doc, process escape sequences
                    match self.process_escapes(line) {
                        Ok(processed_line) => content.push_str(&processed_line),
                        Err(e) => return Some(self.err(e)),
                    }
                } else {
                    // Non-parsed here doc, use content verbatim
                    content.push_str(line);
                }
            }

            if !is_end_of_line {
                // Reached the end of input before finding the delimiter
                // Handle error
                return Some(self.err("unexpected end of input while parsing here doc"));
            }
        }

        let end = self.input.current_byte_index();
        let slice = self.input.slice(start..end);

        Some(Ok(Lexeme {
            token_type: LexemeType::HereString,
            value: Some(LexemeValue::String(content)),
            lex: slice,
            pos: start_pos,
        }))
    }

    /// Helper function to process escape sequences.
    fn process_escapes(&self, input_str: &str) -> Result<String, &'static str> {
        let mut processed_string = String::new();
        let mut chars = input_str.chars().peekable();

        while let Some(ch) = chars.next() {
            if ch == '\\' {
                if let Some(next_ch) = chars.next() {
                    match next_ch {
                        'n' => processed_string.push('\n'),
                        't' => processed_string.push('\t'),
                        'r' => processed_string.push('\r'),
                        'b' => processed_string.push('\u{0008}'), // Backspace
                        'f' => processed_string.push('\u{000C}'), // Form feed
                        '\\' => processed_string.push('\\'),
                        '"' => processed_string.push('"'),
                        '\'' => processed_string.push('\''),
                        'u' => {
                            // Handle Unicode escape sequences
                            let mut unicode_value = 0u32;
                            for _ in 0..4 {
                                if let Some(hex_digit) = chars.next() {
                                    if let Some(digit) = hex_digit.to_digit(16) {
                                        unicode_value = (unicode_value << 4) | digit;
                                    } else {
                                        // Invalid Unicode escape sequence
                                        return Err("Invalid Unicode escape sequence");
                                    }
                                } else {
                                    // Unexpected end of input
                                    return Err("Unexpected end of input in Unicode escape sequence");
                                }
                            }
                            if let Some(unicode_char) = std::char::from_u32(unicode_value) {
                                processed_string.push(unicode_char);
                            } else {
                                return Err("Invalid Unicode code point");
                            }
                        }
                        _ => {
                            // Unknown escape sequence
                            return Err("Unknown escape sequence");
                        }
                    }
                } else {
                    // Single backslash at end of line
                    return Err("Incomplete escape sequence at end of line");
                }
            } else {
                processed_string.push(ch);
            }
        }
        Ok(processed_string)
    }

    /// Parses operators, matching the longest match.
    fn parse_operator(&mut self) -> LexerResult {
        let start = self.input.current_byte_index();
        let mut found_op = None;
        let mut found_op_len = 0;

        let input_end = self.input.len();
        let max_len = self.operators.iter().next().map_or(0, |s| s.len());
        let start_string = self.input.read(max_len);
        for op in self.operators.iter() {
            let op_len = op.len();
            let end = start + op_len;
            if end <= input_end {
                if &start_string[..end - start] == *op {
                    found_op = Some(op);
                    found_op_len = op_len;
                    break; // Since operators are sorted by length, we can break here
                }
            }
        }
        if let Some(_) = found_op {
            // Advance input by longest_len
            for _ in 0..found_op_len {
                if let Err(e) = self.input.peek_char() {
                    let error_message = e.to_string();
                    return self.err(&error_message);
                }
                self.input.step();
            }
            let slice = self.input.slice(start..self.input.current_byte_index());
            Ok(Lexeme {
                token_type: LexemeType::Operator,
                value: None,
                lex: slice,
                pos: self.input.pos.clone(),
            })
        } else {
            if let Err(e) = self.input.peek_char() {
                let error_message = e.to_string();
                return self.err(&error_message);
            }
            self.input.step();
            let slice = self.input.slice(start..self.input.current_byte_index());
            Ok(Lexeme {
                token_type: LexemeType::SingleCharacter,
                value: None,
                lex: slice,
                pos: self.input.pos.clone(),
            })
        }
    }

    /// Parses whitespace as a lexeme.
    fn parse_whitespace(&mut self) -> LexerResult {
        let start = self.input.current_byte_index();
        while let Ok(Some(ch)) = self.input.peek_char() {
            if ch.is_whitespace() && (self.config.treat_newline_as_whitespace || ch != '\n') {
                self.input.step();
            } else {
                break;
            }
        }
        let end = self.input.current_byte_index();
        let slice = self.input.slice(start..end);

        Ok(Lexeme {
            token_type: LexemeType::Whitespace,
            value: None,
            lex: slice,
            pos: self.input.pos.clone(),
        })
    }

    /// Parses newlines as a lexeme.
    fn parse_newline(&mut self) -> LexerResult {
        let start = self.input.current_byte_index();
        self.input.step(); // Consume the newline character
        let end = self.input.current_byte_index();
        let slice = self.input.slice(start..end);

        Ok(Lexeme {
            token_type: LexemeType::Newline,
            value: None,
            lex: slice,
            pos: self.input.pos.clone(),
        })
    }
}

impl Lexeme {
    pub fn equals(&self, s: &str) -> bool {
        self.lex == s
    }

    pub fn is_number(&self) -> bool {
        self.token_type == LexemeType::FloatLiteral || self.token_type == LexemeType::IntegerLiteral
    }

    pub fn is_float(&self) -> bool {
        self.token_type == LexemeType::FloatLiteral
    }

    pub fn is_integer(&self) -> bool {
        self.token_type == LexemeType::IntegerLiteral
    }

    pub fn is_string(&self) -> bool {
        self.token_type == LexemeType::DoubleQuotedString
            || self.token_type == LexemeType::SingleQuotedString
            || self.token_type == LexemeType::TripleDoubleQuotedString
            || self.token_type == LexemeType::TripleSingleQuotedString
            || self.token_type == LexemeType::HereString
    }

    pub fn is_operator(&self) -> bool {
        self.token_type == LexemeType::Operator
    }

    pub fn is_identifier(&self) -> bool {
        self.token_type == LexemeType::Identifier
    }

    pub fn is_keyword(&self) -> bool {
        self.token_type == LexemeType::Keyword
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::LexemeType::{HereString, Newline, IntegerLiteral, FloatLiteral, Operator, SingleCharacter, Keyword, Identifier, Whitespace};
    use super::*;

    impl Lexer {
        fn for_test() -> Self {
            Lexer::new(
                Input::from_string(r#""#).expect("Could create temp test file."),
                HashSet::from([]),
                Vec::from([]),
                LexerConfig {
                    skip_whitespace: true,
                    treat_newline_as_whitespace: true,
                },
            )
        }
        fn input(mut self, input: &str) -> Self {
            self.input = Input::from_string(input).expect("Could create temp test file.");
            self
        }
        fn keywords(mut self, kw: &[&'static str]) -> Self {
            self.keywords = kw.iter().cloned().collect();
            self
        }
        fn operators(mut self, op: &[&'static str]) -> Self {
            self.operators = op.iter().cloned().collect();
            self
        }
        fn newline_sensitive(mut self) -> Self {
            self.config.treat_newline_as_whitespace = false;
            self
        }
        fn whitespace_sensitive(mut self) -> Self {
            self.config.skip_whitespace = false;
            self
        }
    }
    impl PartialEq for LexemeValue {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (LexemeValue::Integer(a), LexemeValue::Integer(b)) => a == b,
                (LexemeValue::Float(a), LexemeValue::Float(b)) => (a - b).abs() < std::f64::EPSILON,
                (LexemeValue::String(a), LexemeValue::String(b)) => a == b,
                _ => false,
            }
        }
    }

    impl Eq for LexemeValue {}

    fn test_lexemes(mut lexer: Lexer, expected: &[(LexemeType, Option<LexemeValue>, &str)]) {
        for &(ref expected_type, ref expected_value, ref expected_slice) in expected {
            match lexer.next_lexeme() {
                Some(Ok(lexeme)) => {
                    assert_eq!(
                        &lexeme.token_type, expected_type,
                        "Expected lexeme type {:?}, found {:?} / {:?} / {:?}",
                        expected_type, lexeme.token_type, lexeme.value, lexeme.lex
                    );
                    assert_eq!(
                        &lexeme.value, expected_value,
                        "Expected lexeme value {:?}, found {:?} / {:?} / {:?}",
                        expected_type, lexeme.token_type, lexeme.value, lexeme.lex
                    );
                    assert_eq!(
                        lexeme.lex, *expected_slice,
                        "Expected lexeme slice {:?}, found {:?} / {:?} / {:?}",
                        expected_type, lexeme.token_type, lexeme.value, lexeme.lex
                    );
                }
                Some(Err(e)) => panic!("Lexer error: {:?}", e),
                None => panic!("Expected lexeme, but lexer produced None"),
            }
        }
        // Verify no extra lexemes
        assert!(
            lexer.next_lexeme().is_none(),
            "Lexer produced extra lexemes beyond expected count"
        );
    }

    #[test]
    fn simple_test_nothing_but_a_bew_line() {
        let lexer = Lexer::for_test().input(
            r#"
"#).newline_sensitive();
        test_lexemes(lexer, &[(Newline, None, "\n")]);
    }

    fn test_here_document(header: &str, doc: &str, footer: &str) {
        let here_doc = &format!("{}\n{}\n{}\n", header, doc, footer)[..];
        let lexer = Lexer::for_test().input(&here_doc).newline_sensitive();
        test_lexemes(lexer, &[(HereString, Some(LexemeValue::String(doc.to_string())), &here_doc)]);
    }


    #[test]
    fn paste_here_string_double_quoted() {
        test_here_document("<<\"EOF\"", "This is a here doc", "EOF");
    }

    #[test]
    fn paste_here_string_double_quoted_spaces_after() {
        test_here_document("<<\"EOF\"   \r", "This is a here doc", "EOF");
    }

    #[test]
    fn paste_here_string_no_quoted() {
        test_here_document("<<EOF", "This is a here doc", "EOF");
    }

    #[test]
    fn paste_here_string_single_quoted() {
        test_here_document("<<'EOF'", "This is a here doc", "EOF");
    }

    #[test]
    fn paste_here_string_single_quoted_spaces_after() {
        test_here_document("<<'EOF'   ", "This is a here doc", "EOF");
    }

    #[test]
    fn paste_here_string_single_quoted_spaces_in_closing() {
        test_here_document("<<'EOF'", "This is a here doc", "EOF   ");
    }


    fn test_quoted_string(quote: &str, doc: &str, res: &str) {
        let t = match quote {
            "\"" => LexemeType::DoubleQuotedString,
            "'" => LexemeType::SingleQuotedString,
            "\"\"\"" => LexemeType::TripleDoubleQuotedString,
            "'''" => LexemeType::TripleSingleQuotedString,
            _ => panic!("Unknown quote type"),
        };
        let string = &format!("{}{}{}", quote, doc, quote)[..];
        let lexer = Lexer::for_test().input(&string).newline_sensitive();
        test_lexemes(lexer, &[(t, Some(LexemeValue::String(res.to_string())), &string)]);
    }

    #[test]
    fn test_single_quoted_string() {
        test_quoted_string("'", "This is \\nhere doc", "This is \\nhere doc");
    }
    #[test]
    fn test_double_quoted_string() {
        test_quoted_string("\"", "This is \\nhere doc", "This is \nhere doc");
    }
    #[test]
    fn test_double_quoted_emptystring() {
        test_quoted_string("\"", "", "");
    }
    #[test]
    fn test_triple_single_quoted_string() {
        test_quoted_string("'''", "This is \\nhere doc", "This is \\nhere doc");
    }
    #[test]
    fn test_triple_double_quoted_string() {
        test_quoted_string("\"\"\"", "This is \n\\nhere doc", "This is \n\nhere doc");
    }

    fn test_error(string: &str, er: &str) {
        let mut lexer = Lexer::for_test().input(&string).newline_sensitive();
        match lexer.next_lexeme() {
            Some(Err(e)) => {
                assert_eq!(e.message, er);
            }
            _ => panic!("Expected error, but got lexeme"),
        }
    }

    #[test]
    fn terminated_delimiter() {
        test_error("<<EOF", "unexpected eof in delimiter");
    }
    #[test]
    fn newline_in_dq_delimiter() {
        test_error("<<\"EOF\nEOR\"\nkabakukk\nEOF", "unexpected newline in delimiter");
    }
    #[test]
    fn newline_in_sq_delimiter() {
        test_error("<<\'EOF\nEOR'\nkabakukk\nEOF", "unexpected newline in delimiter");
    }
    #[test]
    fn unterminated_here_doc() {
        test_error("<<\'EOF'\nkabakukk\nFOE", "unexpected end of input while parsing here doc");
    }

    fn test_parse_integer(string: &str, value: i64) {
        let lexer = Lexer::for_test().input(&string).newline_sensitive();
        test_lexemes(lexer, &[(IntegerLiteral, Some(LexemeValue::Integer(value)), string)]);
    }

    #[test]
    fn parse_666() {
        test_parse_integer("666", 666);
    }
    #[test]
    fn parse_0666() {
        test_parse_integer("0666", 666);
    }
    #[test]
    fn parse_0x666() {
        test_parse_integer("0x666", 1638);
    }
    #[test]
    fn parse_0x_fe() {
        test_parse_integer("0xFE", 254);
        test_parse_integer("0xfe", 254);
    }
    #[test]
    fn parse_0o66() {
        test_parse_integer("0o66", 54);
    }
    #[test]
    fn parse_0b110101() {
        test_parse_integer("0b110101", 53);
    }

    fn test_parse_float(string: &str, value: f64) {
        let lexer = Lexer::for_test().input(&string).newline_sensitive();
        test_lexemes(lexer, &[(FloatLiteral, Some(LexemeValue::Float(value)), string)]);
    }

    #[test]
    fn parse_666point5() {
        test_parse_float("666.5", 666.5);
    }
    #[test]
    fn parse_666point5e13() {
        test_parse_float("666.5e13", 666.5E13);
    }
    #[test]
    fn parse_666point5ep13() {
        test_parse_float("666.5e13", 666.5E+13);
    }
    #[test]
    fn parse_666point5em13() {
        test_parse_float("666.5e-13", 666.5E-13);
    }

    #[test]
    fn test_operators() {
        let lexer = Lexer::for_test().input(r#"+ ++ += - -- -= * *= / /= == != < > <= >= ==="#)
            .operators(&["++", "+=", "--", "-=", "*=", "/=", "==", "!=", "<=", ">=",
                "+", "-", "*", "/", "<", ">", ]);
        test_lexemes(lexer, &[(Operator, None, "+"), (Operator, None, "++"), (Operator, None, "+="),
            (Operator, None, "-"), (Operator, None, "--"), (Operator, None, "-="),
            (Operator, None, "*"), (Operator, None, "*="), (Operator, None, "/"),
            (Operator, None, "/="), (Operator, None, "=="), (Operator, None, "!="),
            (Operator, None, "<"), (Operator, None, ">"), (Operator, None, "<="),
            (Operator, None, ">="),
            (Operator, None, "=="),
            (SingleCharacter, None, "="),
        ]);
    }
    #[test]
    fn test_keywords() {
        let lexer = Lexer::for_test().input(r#"
if then else let const default"#)
            .keywords(&["if", "then", "else", "let", "const", "var"]);
        test_lexemes(lexer, &[
            (Keyword, None, "if"),
            (Keyword, None, "then"),
            (Keyword, None, "else"),
            (Keyword, None, "let"),
            (Keyword, None, "const"),
            (Identifier, None, "default"),
        ]);
    }
    #[test]
    fn test_newline_and_space() {
        let lexer = Lexer::for_test().input("\nif  then else")
            .whitespace_sensitive().newline_sensitive();
        test_lexemes(lexer, &[
            (Newline, None, "\n"),
            (Identifier, None, "if"),
            (Whitespace, None, "  "),
            (Identifier, None, "then"),
            (Whitespace, None, " "),
            (Identifier, None, "else"),
        ]);
    }
    #[test]
    fn test_no_newline_and_space() {
        let lexer = Lexer::for_test().input("\n if  then else")
            .whitespace_sensitive();
        test_lexemes(lexer, &[
            (Whitespace, None, "\n "),
            (Identifier, None, "if"),
            (Whitespace, None, "  "),
            (Identifier, None, "then"),
            (Whitespace, None, " "),
            (Identifier, None, "else"),
        ]);
    }
}
