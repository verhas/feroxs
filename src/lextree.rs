use std::collections::HashMap;
use crate::lexer::{Lexeme, LexemeType, Lexer};

/// Represents a hierarchical structure of parsed lexemes, where each node can be either a single lexeme
/// or a subtree containing a collection of lexemes.
///
/// # Fields
/// - `tree_type`: An optional `Lexeme` that signifies the type or category of the tree's root (e.g., an operator or keyword).
/// - `children`: A vector of `Node` elements representing either individual lexemes or nested subtrees.
pub struct LexTree {
    pub tree_type: Option<Lexeme>,
    pub children: Vec<Node>,
}

/// Enum representing a node within the `LexTree`.
/// A node can be a single `Lexeme` or a subtree (`LexTree`) containing other nodes.
pub enum Node {
    Lexeme(Lexeme),
    Tree(LexTree),
}

/// Builder for constructing a `LexTree` from a sequence of lexemes provided by a lexer.
///
/// # Fields
/// - `lexer`: A `Lexer` instance responsible for supplying lexemes.
/// - `parentheses`: A `HashMap` storing pairs of open and close parenthesis tokens used to define nested structures.
struct LexTreeBuilder {
    lexer: Lexer,
    parentheses: HashMap<&'static str, &'static str>,
}

impl LexTreeBuilder {
    /// Constructs a new `LexTreeBuilder` with the specified lexer and pairs of parentheses tokens.
    ///
    /// # Parameters
    /// - `lexer`: A `Lexer` instance for generating lexemes.
    /// - `parentheses`: A slice of tuple pairs (`&str`, `&str`) representing open and close parenthesis tokens.
    ///
    /// # Returns
    /// A new `LexTreeBuilder` instance with the given lexer and parentheses mappings.
    fn new(lexer: Lexer, parentheses: &[(&str, &str)]) -> LexTreeBuilder {
        LexTreeBuilder {
            lexer,
            parentheses: HashMap::from(parentheses),
        }
    }

    /// Builds the root `LexTree` by initiating the recursive node attachment process.
    ///
    /// # Returns
    /// - `Ok(LexTree)`: The root lexeme tree constructed from the lexer's tokens.
    /// - `Err(String)`: An error message if an error occurs during lexeme processing.
    pub fn build_tree(&mut self) -> Result<LexTree, String> {
        let mut root = LexTree {
            tree_type: None,
            children: Vec::new(),
        };
        match self.hang_nodes(&mut root) {
            Ok(_) => Ok(root),
            Err(e) => Err(e),
        }
    }

    /// Recursively processes lexemes from the lexer and attaches them to the specified `parent` tree.
    /// This function organizes tokens into nested subtrees according to the parentheses mappings.
    ///
    /// # Parameters
    /// - `parent`: A mutable reference to a `LexTree` representing the parent node to which new nodes are attached.
    ///
    /// # Returns
    /// - `Ok(&mut LexTree)`: The modified parent tree with new nodes attached.
    /// - `Err(String)`: An error message if lexeme processing encounters an error.
    pub fn hang_nodes(&mut self, parent: &mut LexTree) -> Result<&mut LexTree, String> {
        // Determine the closing parenthesis for the current tree, if applicable.
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
                            // Check if the lexeme is the closing parenthesis of the current tree.
                            if let Some(closing_parenthesis) = closer {
                                if &lexeme.lex == closing_parenthesis {
                                    return Ok(parent);
                                }
                            }
                            // Start a new subtree if the lexeme is an opening parenthesis.
                            if self.parentheses.contains_key(&lexeme.lex.as_str()) {
                                let mut tree = LexTree {
                                    tree_type: Some(lexeme),
                                    children: Vec::new(),
                                };
                                self.hang_nodes(&mut tree)?;
                                parent.children.push(Node::Tree(tree));
                            } else {
                                parent.children.push(Node::Lexeme(lexeme));
                            }
                        }
                        _ => parent.children.push(Node::Lexeme(lexeme)),
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
