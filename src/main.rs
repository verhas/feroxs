use std::collections::{BTreeSet, HashSet};

mod input;
mod lexer;

use input::{Input};
use crate::lexer::{Lexer, LexerConfig};

fn main() {
    let input = Input::new("src/main.rs").expect("Could not read file.");
    let mut lexer = Lexer::new(
        input,
        HashSet::from([
            "if", "else", "for", "while", "return", // add all your keywords here
        ]),
        BTreeSet::from([
           ".", "+", "-", "*", "/", "==", "!=", "<", ">", "<=", ">=", // add all your operators here
        ]),
        LexerConfig {
            skip_whitespace: true,
            treat_newline_as_whitespace: false,
        },
    );
    println!("Here we go:\n");
    let mut i = 0;
    loop {
        match lexer.next_lexeme() {
            Some(Ok(lexeme)) => {
                i += 1;
                println!("{i}. {:?} : {:?} {}", lexeme.pos, lexeme.token_type, lexeme.slice);
            }
            Some(Err(e)) => {
                println!("Error: {}", e.message);
                return;
            }
            None => {
                break;
            }
        }
    }
    println!("Done!");
}