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
    fn new(lexer: Lexer, parentheses: &[(&'static str, &'static str)]) -> LexTreeBuilder {
        LexTreeBuilder {
            lexer,
            parentheses: parentheses.iter().cloned().collect(),
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

#[cfg(test)]
mod lextree_tests {
    use super::*;
    use crate::lexer::{Lexer, LexerConfig, LexemeType};
    use std::collections::{HashSet};
    use crate::input::Input;

    // Helper function to create a lexer for testing
    fn create_lexer(input: &str) -> Lexer {
        let keywords = HashSet::from(["if", "else", "while"]);
        let operators = vec!["(", ")", "{", "}", "+", "-", "*", "/", "=="];
        Lexer::new(
            Input::from_string(input).expect("Failed to create Input"),
            keywords,
            operators,
            LexerConfig {
                skip_whitespace: true,
                treat_newline_as_whitespace: true,
            },
        )
    }

    #[test]
    fn test_simple_expression_tree() {
        let lexer = create_lexer("if (x == 5) { y = x + 1 }");
        let mut builder = LexTreeBuilder::new(lexer, &[("(", ")"), ("{", "}")]);

        let tree = builder.build_tree().expect("Failed to build tree");

        assert_eq!(tree.children.len(), 3, "Tree should have 3 main children");

        match &tree.children[0] {
            Node::Lexeme(lexeme) => {
                assert_eq!(lexeme.token_type, LexemeType::Keyword);
                assert_eq!(lexeme.lex, "if");
            }
            _ => panic!("Expected 'if' keyword lexeme"),
        }

        // Checking the nested condition `(x == 5)`
        if let Node::Tree(condition) = &tree.children[1] {
            assert_eq!(condition.tree_type.as_ref().unwrap().lex, "(", "Expected '(' opening condition");

            let x_lexeme = match &condition.children[0] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(x_lexeme.lex, "x", "Expected 'x' lexeme");

            let equal_op = match &condition.children[1] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(equal_op.lex, "==", "Expected '==' lexeme");

            let five_lexeme = match &condition.children[2] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(five_lexeme.lex, "5", "Expected '5' lexeme");
        } else {
            panic!("Expected subtree for condition");
        }

        // Checking the nested block `{ y = x + 1 }`
        if let Node::Tree(block) = &tree.children[2] {
            assert_eq!(block.tree_type.as_ref().unwrap().lex, "{", "Expected '{{' opening block");

            let y_lexeme = match &block.children[0] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(y_lexeme.lex, "y", "Expected 'y' lexeme");

            let equal_op = match &block.children[1] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(equal_op.lex, "=", "Expected '=' lexeme");

            let x_lexeme = match &block.children[2] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(x_lexeme.lex, "x", "Expected 'x' lexeme");

            let plus_op = match &block.children[3] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(plus_op.lex, "+", "Expected '+' lexeme");

            let one_lexeme = match &block.children[4] {
                Node::Lexeme(l) => l,
                _ => panic!("Expected lexeme"),
            };
            assert_eq!(one_lexeme.lex, "1", "Expected '1' lexeme");
        } else {
            panic!("Expected subtree for block");
        }
    }

    #[test]
    fn test_nested_parentheses_tree() {
        let lexer = create_lexer("((x + y) * z)");
        let mut builder = LexTreeBuilder::new(lexer, &[("(", ")"), ("{", "}")]);

        let tree = builder.build_tree().expect("Failed to build tree");

        assert!(matches!(tree.children[0], Node::Tree(_)), "Expected nested expression tree");

        let level_1 = match &tree.children[0] {
            Node::Tree(tree) => tree,
            _ => panic!("Expected subtree"),
        };
        assert_eq!(level_1.tree_type.as_ref().unwrap().lex, "(", "Expected outer '('");

        let level_2 = match &level_1.children[0] {
            Node::Tree(tree) => tree,
            _ => panic!("Expected inner subtree"),
        };
        assert_eq!(level_2.tree_type.as_ref().unwrap().lex, "(", "Expected inner '('");

        let x_lexeme = match &level_2.children[0] {
            Node::Lexeme(l) => l,
            _ => panic!("Expected lexeme"),
        };
        assert_eq!(x_lexeme.lex, "x", "Expected 'x' lexeme");

        let plus_op = match &level_2.children[1] {
            Node::Lexeme(l) => l,
            _ => panic!("Expected lexeme"),
        };
        assert_eq!(plus_op.lex, "+", "Expected '+' lexeme");

        let y_lexeme = match &level_2.children[2] {
            Node::Lexeme(l) => l,
            _ => panic!("Expected lexeme"),
        };
        assert_eq!(y_lexeme.lex, "y", "Expected 'y' lexeme");

        // Check the outermost multiplication
        let mult_op = match &level_1.children[1] {
            Node::Lexeme(l) => l,
            _ => panic!("Expected lexeme"),
        };
        assert_eq!(mult_op.lex, "*", "Expected '*' lexeme");

        let z_lexeme = match &level_1.children[2] {
            Node::Lexeme(l) => l,
            _ => panic!("Expected lexeme"),
        };
        assert_eq!(z_lexeme.lex, "z", "Expected 'z' lexeme");
    }

    #[test]
    fn test_unmatched_parentheses_error() {
        let lexer = create_lexer("(x + (y * z)");
        let mut builder = LexTreeBuilder::new(lexer, &[("(", ")"), ("{", "}")]);

        let result = builder.build_tree();
        assert!(result.is_err(), "Expected unmatched parentheses error");
    }
}

