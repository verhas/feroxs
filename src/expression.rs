// create an expression out of a lextree
//
// lextreee already contains lexemes and nodes.
//
// An expression is
// expression ::= level-1-expression
// ...
// level-i-expression ::= level-(i+1)-expression (operator-precendence-i level-i-expression)*
// ...
// term ::== unary-operator* atom
// atom ::== identifier | keyword | number | string | node
//

use std::collections::HashMap;
use std::fmt;
use crate::lextree::{LexTreeNode};
use crate::lexer::{LexemeType, Lexeme, LexemeValue};
use crate::VecWalker::VecWalker;

struct Expression {
    unary_operators: Vec<String>,
    operators: Vec<String>,
    expressions: Vec<Atom>,
}

enum Atom {
    Identifier(String),
    Keyword(String),
    Float(f64),
    Integer(i64),
    String(String),
    Node(LexTreeNode),
    Expression(Expression), // an expression enclosed between some parentheses
}

impl fmt::Debug for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Identifier(value) => write!(f, "${}", value),
            Atom::Keyword(value) => write!(f, "{}", value),
            Atom::Float(value) => write!(f, "{:.2}", value),
            Atom::Integer(value) => write!(f, "{}", value),
            Atom::String(value) => write!(f, "\"{}\"", value),
            Atom::Node(value) => write!(f, "Node: {:?}", value),
            Atom::Expression(value) => write!(f, "{:?}", value),
        }
    }
}

impl Atom {
    pub fn expression(operators: Vec<String>, mut expressions: Vec<Atom>) -> Atom {
        if operators.len() == 0 && expressions.len() == 1 {
            expressions.pop().unwrap()
        } else {
            Atom::Expression(Expression { unary_operators: Vec::new(), operators, expressions })
        }
    }
    pub fn term(unary_operators: Vec<String>, mut expressions: Vec<Atom>) -> Atom {
        if unary_operators.len() == 0 && expressions.len() == 1 {
            expressions.pop().unwrap()
        } else {
            Atom::Expression(Expression { unary_operators, operators: Vec::new(), expressions })
        }
    }
}

// The collection of the binary operators.
// The key is the operator, the value is the precedence.
// The precedence is a number, the higher the number, the higher the precedence.
// The lowest precedence is 0.
struct BinaryOperators {
    operators: HashMap<String, u32>,
    maximum_precedence: u32,
}

// The collection of the unary operators.
// They are always prefix, and they do not have precedence.
// They are evaluated from right to left.
struct UnaryOperators {
    operators: Vec<String>,
}

struct ExpressionBuilder {
    binary_operators: BinaryOperators,
    unary_operators: UnaryOperators,
    // Only the opening parentheses are stored
    // The closing parentheses are already processed by the lex tree builder.
    // We only have to know the type of the opening parentheses that can appear in an expression.
    // If any block comes not listed here, then the analysis will stop there.
    // A typical example is the curly braces that are used for blocks.
    // Normal parentheses and square brackets are usually used for expressions, but curly braces are not.
    parentheses: Vec<String>,
}


impl ExpressionBuilder {
    pub fn new(binary_operators: &[(u32, &[&'static str])], unary_operators: &[&'static str], parentheses: &[&'static str]) -> ExpressionBuilder {
        let mut operators = HashMap::new();
        let mut maximum_precedence = 0;
        for (precedence, ops) in binary_operators {
            if *precedence > maximum_precedence {
                maximum_precedence = *precedence;
            }
            for &operator in *ops {
                operators.insert(operator.to_string(), *precedence);
            }
        }
        let binary_operators = BinaryOperators { operators, maximum_precedence };

        let mut operators: Vec<String> = Vec::new();
        for &op in unary_operators {
            operators.push(op.to_string());
        }
        let unary_operators = UnaryOperators { operators };

        let mut ps: Vec<String> = Vec::new();
        for &p in parentheses {
            ps.push(p.to_string());
        }
        let parentheses = ps;

        ExpressionBuilder {
            binary_operators,
            unary_operators,
            parentheses,
        }
    }

    fn make_atom_result(mut expressions: Vec<Atom>, operators: Vec<String>) -> Result<Atom, String> {
        if operators.len() == 0 && expressions.len() == 1 {
            Ok(expressions.pop().unwrap())
        } else {
            Ok(Atom::expression(operators, expressions))
        }
    }

    /// Parses a LexTree and returns an Expression.
    pub fn build(&self, iterator: &mut VecWalker<LexTreeNode>) -> Result<Atom, String> {
        self.build_level(iterator, 0)
    }
    pub fn build_level(&self, iterator: &mut VecWalker<LexTreeNode>, level: u32) -> Result<Atom, String> {
        let mut expressions: Vec<Atom> = Vec::new();
        let mut operators: Vec<String> = Vec::new();

        if level == self.binary_operators.maximum_precedence {
            return self.build_term(iterator);
        }
        match self.build_level(iterator, level + 1) {
            Ok(expression) => expressions.push(expression),
            Err(e) => return Err(e),
        }

        while let Some(operation) = iterator.next() {
            match operation {
                LexTreeNode::Tree(subtree) => {
                    operators.push(subtree.subtree_parenthesis());
                    let mut iterator = VecWalker::new(&subtree.children);
                    match self.build(&mut iterator) {
                        Ok(expression) => expressions.push(expression),
                        Err(e) => return Err(e),
                    }
                    if iterator.peek().is_some() {
                        return Err("Unexpected node after expression".to_string());
                    }
                }
                LexTreeNode::Lexeme(lexeme) => {
                    match lexeme.token_type {
                        LexemeType::Operator => {
                            if !self.binary_operators.operators.contains_key(&lexeme.lex) || self.binary_operators.operators[&lexeme.lex] < level {
                                iterator.previous();
                                return Ok(Atom::expression(operators, expressions));
                            } else {
                                operators.push(lexeme.lex.clone());
                                match self.build_level(iterator, level + 1) {
                                    Ok(expression) => expressions.push(expression),
                                    Err(e) => return Err(e),
                                }
                            }
                        }
                        _ => {
                            iterator.previous();
                            return Ok(Atom::expression(operators, expressions));
                        }
                    }
                }
            }
        }
        Ok(Atom::expression(operators, expressions))
    }

    /// Parses a LexTree and returns a Term.
    pub fn build_term(&self, iterator: &mut VecWalker<LexTreeNode>) -> Result<Atom, String> {
        let mut unary_operators = Vec::new();
        let mut atoms = Vec::new();

        while let Some(lexeme) = iterator.next() {
            match lexeme {
                LexTreeNode::Tree(subtree) => {
                    unary_operators.push(subtree.subtree_parenthesis());
                    let mut iterator = VecWalker::new(&subtree.children);
                    match self.build(&mut iterator) {
                        Ok(expression) => atoms.push(expression),
                        Err(e) => return Err(e),
                    }
                    if iterator.peek().is_some() {
                        return Err("Unexpected node after term".to_string());
                    }
                    return Ok(Atom::term(unary_operators, atoms));
                }
                LexTreeNode::Lexeme(lexeme) =>
                    match lexeme.token_type {
                        LexemeType::Operator => {
                            if !self.unary_operators.operators.contains(&lexeme.lex) {
                                return Self::make_atom_result(atoms, unary_operators);
                            }
                            unary_operators.push(lexeme.lex.clone());
                        }
                        _ => return
                            match ExpressionBuilder::build_atom(&lexeme) {
                                Ok(atom) => {
                                    atoms.push(atom);
                                    Ok(Atom::term(unary_operators, atoms))
                                }
                                Err(e) => {
                                    iterator.previous();
                                    Err(e)
                                }
                            }
                    }
            }
        }

        Ok(Atom::term(unary_operators, atoms))
    }

    /// Converts a single Lexeme into an Atom.
    pub fn build_atom(lexeme: &Lexeme) -> Result<Atom, String> {
        match lexeme.token_type {
            LexemeType::Identifier => {
                Ok(Atom::Identifier(lexeme.lex.clone()))
            }
            LexemeType::Keyword => Ok(Atom::Keyword(lexeme.lex.clone())),
            LexemeType::IntegerLiteral => {
                if let Some(LexemeValue::Integer(val)) = &lexeme.value {
                    Ok(Atom::Integer(*val))
                } else {
                    Err(format!("Invalid value for IntegerLiteral: {:?}", lexeme.value))
                }
            }
            LexemeType::FloatLiteral => {
                if let Some(LexemeValue::Float(val)) = &lexeme.value {
                    Ok(Atom::Float(*val))
                } else {
                    Err(format!("Invalid value for FloatLiteral: {:?}", lexeme.value))
                }
            }
            LexemeType::DoubleQuotedString | LexemeType::SingleQuotedString |
            LexemeType::HereString | LexemeType::TripleDoubleQuotedString |
            LexemeType::TripleSingleQuotedString => {
                if let Some(LexemeValue::String(val)) = &lexeme.value {
                    Ok(Atom::String(val.clone()))
                } else {
                    Err(format!("Invalid value for String: {:?}", lexeme.value))
                }
            }
            LexemeType::Operator => Err(String::from("Unexpected lexeme type for Atom: an Operator")),
            LexemeType::Whitespace => Err(String::from("Unexpected lexeme type for Atom: an Whitespace")),
            LexemeType::Newline => Err(String::from("Unexpected lexeme type for Atom: an Newline")),
            LexemeType::SingleCharacter => Err(String::from("Unexpected lexeme type for Atom: an SingleCharacter")),
        }
    }
}

#[cfg(test)]
mod expression_tests {
    use crate::lexer::{Lexer, LexerConfig};
    use crate::lextree::{LexTree, LexTreeBuilder};
    use crate::expression::{Expression, ExpressionBuilder};
    use std::collections::HashSet;
    use std::fmt;
    use crate::input::Input;
    use crate::VecWalker::VecWalker;

    // a special debug implementation for Expression only used for testing purposes
    impl fmt::Debug for Expression {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "(").expect("no write");
            self.unary_operators.iter().for_each(|op| write!(f, "{:?}", op).expect("no write"));
            write!(f, "{:?}", self.expressions.first().unwrap()).expect("no write");
            self.operators.iter().zip(self.expressions.iter().skip(1)).for_each(|(op, expr)| {
                write!(f, " {} {:?}", op, expr).unwrap();
            });
            write!(f, ")").expect("no write");
            Ok(())
        }
    }

    fn create_lex_tree_builder(input: &str) -> LexTreeBuilder {
        let keywords = HashSet::from(["if", "else", "while"]);
        let operators = vec!["==", "[", "]", "{", "}", "+", "-", "*", "/", ];
        let lexer = Lexer::new(
            Input::from_string(input).expect("Failed to create Input"),
            keywords,
            operators,
            LexerConfig {
                skip_whitespace: true,
                treat_newline_as_whitespace: true,
            },
        );

        // '(' and ')' are used for debugging in the tests
        LexTreeBuilder::new(lexer, &[("[", "]"), ("{", "}")])
    }

    fn test_expression_builder(expression: &str, result_dump: &str) {
        let lbt = create_lex_tree_builder(expression).build_tree().expect("Failed to build lexical tree");
        let etb = ExpressionBuilder::new(&[(0, &["+", "-"]), (1, &["*", "/"]), (3, &["=="])], &["+"], &["{", "["]);
        let res = etb.build(&mut VecWalker::new(&lbt.children))
            .expect("Failed to build expression");

        let res_str = format!("{:?}", res);
        assert_eq!(res_str, result_dump);
    }

    // Test constructing a simple expression
    #[test]
    fn test_simple_expression() {
        test_expression_builder("x + y * z", "($x + ($y * $z))");
    }


    #[test]
    fn test_expression_with_parentheses() {
        test_expression_builder("{x + y} * z", "((\"{\"($x + $y)) * $z)");
    }

    #[test]
    fn test_expression_with_nested_parentheses() {
        test_expression_builder("[x + [{y}]] * z", "((\"[\"($x + (\"[\"(\"{\"$y)))) * $z)");
    }

    #[test]
    fn test_expression_with_joined_parts() {
        test_expression_builder("x[23]", "($x [ 23)");
    }
}
