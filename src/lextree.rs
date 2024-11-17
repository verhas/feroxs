use std::collections::HashMap;
use crate::lexer::{Lexeme, LexemeType, Lexer};

pub struct LexTree {
    pub tree_type: Option<Lexeme>,
    pub children: Vec<Node>,
}

pub enum Node {
    Lexeme(Lexeme),
    Tree(LexTree),
}

struct LexTreeBuilder {
    lexer: Lexer,
    parentheses: HashMap<&'static str, &'static str>,
}


impl LexTreeBuilder {
    fn new(lexer: Lexer, parentheses: &[(&str, &str)]) -> LexTreeBuilder {
        LexTreeBuilder {
            lexer,
            parentheses: HashMap::from(parentheses),
        }
    }


    pub fn buld_tree(&mut self) -> Result<LexTree, String> {
        let mut root = LexTree {
            tree_type: None,
            children: Vec::new(),
        };
        match self.hang_nodes(&mut root) {
            Ok(_) => Ok(root),
            Err(e) => Err(e)
        }
    }

    pub fn hang_nodes(&mut self, parent: &mut LexTree) -> Result<&mut LexTree, String> {
        let closer = parent.tree_type.as_ref().and_then(|p| {
            if matches!(p.token_type, LexemeType::Keyword | LexemeType::Operator) {
                self.parentheses.get(p.lex.as_str()).copied()
            } else {
                None
            }
        });

        loop {
            match self.lexer.next_lexeme() {
                Some(Ok(lexeme)) => {
                    match lexeme.token_type {
                        LexemeType::Operator | LexemeType::Keyword => {
                            // if it is the closing parenthesis of the current tree
                            if let Some(closing_parenthesis) = closer {
                                if &lexeme.lex == closing_parenthesis {
                                    return Ok(parent);
                                }
                            }
                            // if it is a new tree
                            if self.parentheses.contains_key(&lexeme.lex.as_str()) {
                                let mut tree = LexTree {
                                    tree_type: Some(lexeme),
                                    children: Vec::new(),
                                };
                                self.hang_nodes(&mut tree);
                                parent.children.push(Node::Tree(tree));
                            } else {
                                parent.children.push(Node::Lexeme(lexeme));
                            }
                        }
                        _ => parent.children.push(Node::Lexeme(lexeme))
                    }
                }
                Some(Err(e)) => {
                    return Err(e.message);
                }
                None => {
                    break;
                }
            }
        }
        Ok(parent)
    }
}

