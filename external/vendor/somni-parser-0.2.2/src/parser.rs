//! Grammar parser.
//!
//! This module parses the following grammar (minus comments, which are ignored):
//!
//! ```text
//! program -> item* EOF;
//! item -> function | global | extern_fn; // TODO types.
//!
//! extern_fn -> 'extern' 'fn' identifier '(' function_argument ( ',' function_argument )* ','? ')' return_decl? ;
//! global -> 'var' identifier ':' type '=' static_initializer ';' ;
//!
//! static_initializer -> right_hand_expression ; // The language does not currently support function calls.
//!
//! function -> 'fn' identifier '(' function_argument ( ',' function_argument )* ','? ')' return_decl? body ;
//! function_argument -> identifier ':' '&'? type ;
//! return_decl -> '->' type ;
//! type -> identifier ;
//!
//! body -> '{' statement '}' ;
//! statement -> 'var' identifier (':' type)? '=' right_hand_expression ';' (statement)?
//!            | 'return' right_hand_expression? ';' (statement)?
//!            | 'break' ';' (statement)?
//!            | 'continue' ';' (statement)?
//!            | 'if' right_hand_expression body ( 'else' body )? (statement)?
//!            | 'loop' body (statement)?
//!            | 'while' right_hand_expression body (statement)?
//!            | body (statement)?
//!            | expression ';' (statement)?
//!            | right_hand_expression // implicit return statmenet
//!
//! expression -> (left_hand_expression '=')? right_hand_expression ;
//!
//! left_hand_expression -> ( '*' )? identifier ; // Should be a valid expression, too.
//!
//! right_hand_expression -> binary2 ( '||' binary2 )* ;
//! binary2 -> binary3 ( '&&' binary3 )* ;
//! binary3 -> binary4 ( ( '<' | '<=' | '>' | '>=' | '==' | '!=' ) binary4 )* ;
//! binary4 -> binary5 ( '|' binary5 )* ;
//! binary5 -> binary6 ( '^' binary6 )* ;
//! binary6 -> binary7 ( '&' binary7 )* ;
//! binary7 -> binary8 ( ( '<<' | '>>' ) binary8 )* ;
//! binary8 -> binary9 ( ( '+' | '-' ) binary9 )* ;
//! binary9 -> unary ( ( '*' | '/', '%' ) unary )* ;
//! unary -> ('!' | '-' | '&' | '*' )* primary | call ;
//! primary -> ( literal | identifier ( '(' call_arguments ')' )? ) | '(' right_hand_expression ')' ;
//! call_arguments -> right_hand_expression ( ',' right_hand_expression )* ','? ;
//! literal -> NUMBER | STRING | 'true' | 'false' ;
//! ```
//!
//! `NUMBER`: Non-negative integers (binary, decimal, hexadecimal) and floats.
//! `STRING`: Double-quoted strings with escape sequences.

use std::{
    fmt::{Debug, Display},
    num::{ParseFloatError, ParseIntError},
    ops::ControlFlow,
};

use crate::{
    ast::{
        Body, Break, Continue, Else, EmptyReturn, Expression, ExternalFunction, Function,
        FunctionArgument, GlobalVariable, If, Item, LeftHandExpression, Literal, LiteralValue,
        Loop, Program, ReturnDecl, ReturnWithValue, RightHandExpression, Statement, TypeHint,
        VariableDefinition,
    },
    lexer::{Token, TokenKind, Tokenizer},
    parser::private::Sealed,
    Error, Location,
};

mod private {
    pub trait Sealed {}

    impl Sealed for u32 {}
    impl Sealed for u64 {}
    impl Sealed for u128 {}
    impl Sealed for f32 {}
    impl Sealed for f64 {}
}

/// Parse literals into Somni integers.
pub trait IntParser: Sized + Sealed {
    fn parse(str: &str, radix: u32) -> Result<Self, ParseIntError>;
}

impl IntParser for u32 {
    fn parse(str: &str, radix: u32) -> Result<Self, ParseIntError> {
        u32::from_str_radix(str, radix)
    }
}
impl IntParser for u64 {
    fn parse(str: &str, radix: u32) -> Result<Self, ParseIntError> {
        u64::from_str_radix(str, radix)
    }
}
impl IntParser for u128 {
    fn parse(str: &str, radix: u32) -> Result<Self, ParseIntError> {
        u128::from_str_radix(str, radix)
    }
}

/// Parse literals into Somni floats.
pub trait FloatParser: Sized + Sealed {
    fn parse(str: &str) -> Result<Self, ParseFloatError>;
}

impl FloatParser for f32 {
    fn parse(str: &str) -> Result<Self, ParseFloatError> {
        str.parse::<f32>()
    }
}
impl FloatParser for f64 {
    fn parse(str: &str) -> Result<Self, ParseFloatError> {
        str.parse::<f64>()
    }
}

/// Defines the numeric types used in the parser.
pub trait TypeSet: Debug + Default {
    type Integer: IntParser + Clone + Copy + PartialEq + Debug;
    type Float: FloatParser + Clone + Copy + PartialEq + Debug;
}

/// Use 64-bit integers and 64-bit floats (default).
#[derive(Debug, Default)]
pub struct DefaultTypeSet;
impl Sealed for DefaultTypeSet {}

impl TypeSet for DefaultTypeSet {
    type Integer = u64;
    type Float = f64;
}

/// Use 32-bit integers and floats.
#[derive(Debug, Default)]
pub struct TypeSet32;
impl Sealed for TypeSet32 {}
impl TypeSet for TypeSet32 {
    type Integer = u32;
    type Float = f32;
}

/// Use 128-bit integers and 64-bit floats.
#[derive(Debug, Default)]
pub struct TypeSet128;
impl Sealed for TypeSet128 {}
impl TypeSet for TypeSet128 {
    type Integer = u128;
    type Float = f64;
}

impl<T> Program<T>
where
    T: TypeSet,
{
    fn parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        let mut items = Vec::new();

        while !stream.end()? {
            items.push(Item::parse(stream)?);
        }

        Ok(Program { items })
    }
}

impl<T> Item<T>
where
    T: TypeSet,
{
    fn parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        if let Some(global_var) = GlobalVariable::try_parse(stream)? {
            return Ok(Item::GlobalVariable(global_var));
        }
        if let Some(function) = ExternalFunction::try_parse(stream)? {
            return Ok(Item::ExternFunction(function));
        }
        if let Some(function) = Function::try_parse(stream)? {
            return Ok(Item::Function(function));
        }

        Err(stream.error("Expected global variable or function definition"))
    }
}

impl<T> GlobalVariable<T>
where
    T: TypeSet,
{
    fn try_parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Option<Self>, Error> {
        let Some(decl_token) = stream.take_match(TokenKind::Identifier, &["var"])? else {
            return Ok(None);
        };

        let identifier = stream.expect_match(TokenKind::Identifier, &[])?;
        let colon = stream.expect_match(TokenKind::Symbol, &[":"])?;
        let type_token = TypeHint::parse(stream)?;
        let equals_token = stream.expect_match(TokenKind::Symbol, &["="])?;
        let initializer = Expression::Expression {
            expression: RightHandExpression::parse(stream)?,
        };
        let semicolon = stream.expect_match(TokenKind::Symbol, &[";"])?;

        Ok(Some(GlobalVariable {
            decl_token,
            identifier,
            colon,
            type_token,
            equals_token,
            initializer,
            semicolon,
        }))
    }
}

impl ExternalFunction {
    fn try_parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Option<Self>, Error> {
        let Some(extern_fn_token) = stream.take_match(TokenKind::Identifier, &["extern"])? else {
            return Ok(None);
        };
        let Some(fn_token) = stream.take_match(TokenKind::Identifier, &["fn"])? else {
            return Ok(None);
        };

        let name = stream.expect_match(TokenKind::Identifier, &[])?;
        let opening_paren = stream.expect_match(TokenKind::Symbol, &["("])?;

        let mut arguments = Vec::new();
        while let Some(arg_name) = stream.take_match(TokenKind::Identifier, &[])? {
            let colon = stream.expect_match(TokenKind::Symbol, &[":"])?;
            let reference_token = stream.take_match(TokenKind::Symbol, &["&"])?;
            let type_token = TypeHint::parse(stream)?;

            arguments.push(FunctionArgument {
                name: arg_name,
                colon,
                reference_token,
                arg_type: type_token,
            });

            if stream.take_match(TokenKind::Symbol, &[","])?.is_none() {
                break;
            }
        }

        let closing_paren = stream.expect_match(TokenKind::Symbol, &[")"])?;

        let return_decl =
            if let Some(return_token) = stream.take_match(TokenKind::Symbol, &["->"])? {
                Some(ReturnDecl {
                    return_token,
                    return_type: TypeHint::parse(stream)?,
                })
            } else {
                None
            };

        let semicolon = stream.expect_match(TokenKind::Symbol, &[";"])?;

        Ok(Some(ExternalFunction {
            extern_fn_token,
            fn_token,
            name,
            opening_paren,
            arguments,
            closing_paren,
            return_decl,
            semicolon,
        }))
    }
}

impl<T> Function<T>
where
    T: TypeSet,
{
    fn try_parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Option<Self>, Error> {
        let Some(fn_token) = stream.take_match(TokenKind::Identifier, &["fn"])? else {
            return Ok(None);
        };

        let name = stream.expect_match(TokenKind::Identifier, &[])?;
        let opening_paren = stream.expect_match(TokenKind::Symbol, &["("])?;

        let mut arguments = Vec::new();
        while let Some(arg_name) = stream.take_match(TokenKind::Identifier, &[])? {
            let colon = stream.expect_match(TokenKind::Symbol, &[":"])?;
            let reference_token = stream.take_match(TokenKind::Symbol, &["&"])?;
            let type_token = TypeHint::parse(stream)?;

            arguments.push(FunctionArgument {
                name: arg_name,
                colon,
                reference_token,
                arg_type: type_token,
            });

            if stream.take_match(TokenKind::Symbol, &[","])?.is_none() {
                break;
            }
        }

        let closing_paren = stream.expect_match(TokenKind::Symbol, &[")"])?;

        let return_decl =
            if let Some(return_token) = stream.take_match(TokenKind::Symbol, &["->"])? {
                Some(ReturnDecl {
                    return_token,
                    return_type: TypeHint::parse(stream)?,
                })
            } else {
                None
            };

        let body = Body::parse(stream)?;

        Ok(Some(Function {
            fn_token,
            name,
            opening_paren,
            arguments,
            closing_paren,
            return_decl,
            body,
        }))
    }
}

impl<T> Body<T>
where
    T: TypeSet,
{
    fn parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        let opening_brace = stream.expect_match(TokenKind::Symbol, &["{"])?;

        let mut body = Vec::new();
        while Statement::<T>::matches(stream)? {
            let (statement, stop) = match Statement::parse(stream)? {
                ControlFlow::Continue(statement) => (statement, false),
                ControlFlow::Break(statement) => (statement, true),
            };
            body.push(statement);
            if stop {
                break;
            }
        }

        let closing_brace = stream.expect_match(TokenKind::Symbol, &["}"])?;

        Ok(Body {
            opening_brace,
            statements: body,
            closing_brace,
        })
    }
}

impl TypeHint {
    fn parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        let type_name = stream.expect_match(TokenKind::Identifier, &[])?;

        Ok(TypeHint { type_name })
    }
}

impl<T> Statement<T>
where
    T: TypeSet,
{
    fn matches(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<bool, Error> {
        stream
            .peek_match(TokenKind::Symbol, &["}"])
            .map(|t| t.is_none())
    }

    fn parse(
        stream: &mut TokenStream<'_, impl Tokenizer>,
    ) -> Result<ControlFlow<Self, Self>, Error> {
        if let Some(return_token) = stream.take_match(TokenKind::Identifier, &["return"])? {
            let return_kind =
                if let Some(semicolon) = stream.take_match(TokenKind::Symbol, &[";"])? {
                    // Continue, parsing unreachable code is allowed
                    Statement::EmptyReturn(EmptyReturn {
                        return_token,
                        semicolon,
                    })
                } else {
                    let expr = RightHandExpression::parse(stream)?;
                    let semicolon = stream.expect_match(TokenKind::Symbol, &[";"])?;
                    Statement::Return(ReturnWithValue {
                        return_token,
                        expression: expr,
                        semicolon,
                    })
                };

            // Continue, parsing unreachable code is allowed
            return Ok(ControlFlow::Continue(return_kind));
        }

        if let Some(decl_token) = stream.take_match(TokenKind::Identifier, &["var"])? {
            let identifier = stream.expect_match(TokenKind::Identifier, &[])?;

            let type_token = if stream.take_match(TokenKind::Symbol, &[":"])?.is_some() {
                Some(TypeHint::parse(stream)?)
            } else {
                None
            };

            let equals_token = stream.expect_match(TokenKind::Symbol, &["="])?;
            let expression = RightHandExpression::parse(stream)?;
            let semicolon = stream.expect_match(TokenKind::Symbol, &[";"])?;

            return Ok(ControlFlow::Continue(Statement::VariableDefinition(
                VariableDefinition {
                    decl_token,
                    identifier,
                    type_token,
                    equals_token,
                    initializer: expression,
                    semicolon,
                },
            )));
        }

        if let Some(if_token) = stream.take_match(TokenKind::Identifier, &["if"])? {
            let condition = RightHandExpression::parse(stream)?;
            let body = Body::parse(stream)?;

            let else_branch =
                if let Some(else_token) = stream.take_match(TokenKind::Identifier, &["else"])? {
                    let else_body = Body::parse(stream)?;

                    Some(Else {
                        else_token,
                        else_body,
                    })
                } else {
                    None
                };

            return Ok(ControlFlow::Continue(Statement::If(If {
                if_token,
                condition,
                body,
                else_branch,
            })));
        }

        if let Some(loop_token) = stream.take_match(TokenKind::Identifier, &["loop"])? {
            let body = Body::parse(stream)?;
            return Ok(ControlFlow::Continue(Statement::Loop(Loop {
                loop_token,
                body,
            })));
        }

        if let Some(while_token) = stream.take_match(TokenKind::Identifier, &["while"])? {
            // Desugar while into loop { if condition { loop_body; } else { break; } }
            let condition = RightHandExpression::parse(stream)?;
            let body = Body::parse(stream)?;
            return Ok(ControlFlow::Continue(Statement::Loop(Loop {
                loop_token: while_token,
                body: Body {
                    opening_brace: body.opening_brace,
                    closing_brace: body.closing_brace,
                    statements: vec![Statement::If(If {
                        if_token: while_token,
                        condition: condition.clone(),
                        body: body.clone(),
                        else_branch: Some(Else {
                            else_token: while_token,
                            else_body: Body {
                                opening_brace: body.opening_brace,
                                closing_brace: body.closing_brace,
                                statements: vec![Statement::Break(Break {
                                    break_token: while_token,
                                    semicolon: while_token,
                                })],
                            },
                        }),
                    })],
                },
            })));
        }

        if let Some(break_token) = stream.take_match(TokenKind::Identifier, &["break"])? {
            let semicolon = stream.expect_match(TokenKind::Symbol, &[";"])?;
            // Continue, unreachable code is allowed
            return Ok(ControlFlow::Continue(Statement::Break(Break {
                break_token,
                semicolon,
            })));
        }
        if let Some(continue_token) = stream.take_match(TokenKind::Identifier, &["continue"])? {
            let semicolon = stream.expect_match(TokenKind::Symbol, &[";"])?;
            // Continue, unreachable code is allowed
            return Ok(ControlFlow::Continue(Statement::Continue(Continue {
                continue_token,
                semicolon,
            })));
        }

        if let Ok(Some(_)) = stream.peek_match(TokenKind::Symbol, &["{"]) {
            return Ok(ControlFlow::Continue(Statement::Scope(Body::parse(
                stream,
            )?)));
        }

        let save = stream.clone();
        let expression = Expression::parse(stream)?;
        match stream.take_match(TokenKind::Symbol, &[";"])? {
            Some(semicolon) => Ok(ControlFlow::Continue(Statement::Expression {
                expression,
                semicolon,
            })),
            None => {
                // No semicolon, re-parse as a right-hand expression
                *stream = save;
                let expression = RightHandExpression::parse(stream)?;

                Ok(ControlFlow::Break(Statement::ImplicitReturn(expression)))
            }
        }
    }
}

impl<T> Literal<T>
where
    T: TypeSet,
{
    fn parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        let token = stream.peek_expect()?;

        let token_source = stream.source(token.location);
        let location = token.location;

        let literal_value = match token.kind {
            TokenKind::BinaryInteger => {
                let token_source = token_source.replace("_", "");
                Self::parse_integer_literal(&token_source[2..], 2)
                    .map_err(|_| stream.error("Invalid binary integer literal"))?
            }
            TokenKind::DecimalInteger => {
                let token_source = token_source.replace("_", "");
                Self::parse_integer_literal(&token_source, 10)
                    .map_err(|_| stream.error("Invalid integer literal"))?
            }
            TokenKind::HexInteger => {
                let token_source = token_source.replace("_", "");
                Self::parse_integer_literal(&token_source[2..], 16)
                    .map_err(|_| stream.error("Invalid hexadecimal integer literal"))?
            }
            TokenKind::Float => {
                let token_source = token_source.replace("_", "");
                <T::Float as FloatParser>::parse(&token_source)
                    .map(LiteralValue::Float)
                    .map_err(|_| stream.error("Invalid float literal"))?
            }
            TokenKind::String => match unescape(&token_source[1..token_source.len() - 1]) {
                Ok(string) => LiteralValue::String(string),
                Err(offset) => {
                    return Err(Error {
                        error: String::from("Invalid escape sequence in string literal")
                            .into_boxed_str(),
                        location: Location {
                            start: token.location.start + offset,
                            end: token.location.start + offset + 1,
                        },
                    });
                }
            },
            TokenKind::Identifier if token_source == "true" => LiteralValue::Boolean(true),
            TokenKind::Identifier if token_source == "false" => LiteralValue::Boolean(false),
            _ => return Err(stream.error("Expected literal (number, string, or boolean)")),
        };

        stream.expect_match(token.kind, &[])?;
        Ok(Self {
            value: literal_value,
            location,
        })
    }

    fn parse_integer_literal(
        token_source: &str,
        radix: u32,
    ) -> Result<LiteralValue<T>, ParseIntError> {
        <T::Integer as IntParser>::parse(token_source, radix).map(LiteralValue::Integer)
    }
}

fn unescape(s: &str) -> Result<String, usize> {
    let mut result = String::new();
    let mut escaped = false;
    for (i, c) in s.char_indices().peekable() {
        if escaped {
            match c {
                'n' => result.push('\n'),
                't' => result.push('\t'),
                '\\' => result.push('\\'),
                '"' => result.push('"'),
                '\'' => result.push('\''),
                _ => return Err(i), // Invalid escape sequence
            }
            escaped = false;
        } else if c == '\\' {
            escaped = true;
        } else {
            result.push(c);
        }
    }

    Ok(result)
}

impl LeftHandExpression {
    fn parse<T: TypeSet>(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        const UNARY_OPERATORS: &[&str] = &["*"];
        let expr = if let Some(operator) = stream.take_match(TokenKind::Symbol, UNARY_OPERATORS)? {
            Self::Deref {
                operator,
                name: Self::parse_name::<T>(stream)?,
            }
        } else {
            Self::Name {
                variable: Self::parse_name::<T>(stream)?,
            }
        };

        Ok(expr)
    }

    fn parse_name<T: TypeSet>(
        stream: &mut TokenStream<'_, impl Tokenizer>,
    ) -> Result<Token, Error> {
        let token = stream.peek_expect()?;
        match token.kind {
            TokenKind::Identifier => {
                // true, false?
                match Literal::<T>::parse(stream) {
                    Ok(_) => Err(Error {
                        error: "Parse error: Literals are not valid on the left-hand side"
                            .to_string()
                            .into_boxed_str(),
                        location: token.location,
                    }),
                    _ => stream
                        .take_match(TokenKind::Identifier, &[])
                        .map(|v| v.unwrap()),
                }
            }
            _ => Err(stream.error("Expected variable name or deref operator")),
        }
    }
}

impl<T> Expression<T>
where
    T: TypeSet,
{
    fn parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        let save = stream.clone();

        let expression = RightHandExpression::<T>::parse(stream)?;

        if let Ok(Some(operator)) = stream.take_match(TokenKind::Symbol, &["="]) {
            // Re-parse as an assignment
            *stream = save;
            let left_expr = LeftHandExpression::parse::<T>(stream)?;
            stream.expect_match(TokenKind::Symbol, &["="])?;
            let right_expr = RightHandExpression::parse(stream)?;

            Ok(Self::Assignment {
                left_expr,
                operator,
                right_expr,
            })
        } else {
            Ok(Self::Expression { expression })
        }
    }
}

impl<T> RightHandExpression<T>
where
    T: TypeSet,
{
    fn parse(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        // We define the binary operators from the lowest precedence to the highest.
        // Each recursive call to `parse_binary` will handle one level of precedence, and pass
        // the rest to the inner calls of `parse_binary`.
        let operators: &[&[&str]] = &[
            &["||"],
            &["&&"],
            &["<", "<=", ">", ">=", "==", "!="],
            &["|"],
            &["^"],
            &["&"],
            &["<<", ">>"],
            &["+", "-"],
            &["*", "/", "%"],
        ];

        Self::parse_binary(stream, operators)
    }

    fn parse_binary(
        stream: &mut TokenStream<'_, impl Tokenizer>,
        binary_operators: &[&[&str]],
    ) -> Result<Self, Error> {
        let Some((current, higher)) = binary_operators.split_first() else {
            unreachable!("At least one operator set is expected");
        };

        let mut expr = if higher.is_empty() {
            Self::parse_unary(stream)?
        } else {
            Self::parse_binary(stream, higher)?
        };

        while let Some(operator) = stream.take_match(TokenKind::Symbol, current)? {
            let rhs = if higher.is_empty() {
                Self::parse_unary(stream)?
            } else {
                Self::parse_binary(stream, higher)?
            };

            expr = Self::BinaryOperator {
                name: operator,
                operands: Box::new([expr, rhs]),
            };
        }

        Ok(expr)
    }

    fn parse_unary(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        const UNARY_OPERATORS: &[&str] = &["!", "-", "&", "*"];
        if let Some(operator) = stream.take_match(TokenKind::Symbol, UNARY_OPERATORS)? {
            let operand = Self::parse_unary(stream)?;
            Ok(Self::UnaryOperator {
                name: operator,
                operand: Box::new(operand),
            })
        } else {
            Self::parse_primary(stream)
        }
    }

    fn parse_primary(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        let token = stream.peek_expect()?;

        match token.kind {
            TokenKind::Identifier => {
                // true, false?
                if let Ok(literal) = Literal::<T>::parse(stream) {
                    return Ok(Self::Literal { value: literal });
                }

                Self::parse_call(stream)
            }
            TokenKind::Symbol if stream.source(token.location) == "(" => {
                stream.take_match(token.kind, &[])?;
                let expr = Self::parse(stream)?;
                stream.expect_match(TokenKind::Symbol, &[")"])?;
                Ok(expr)
            }
            TokenKind::HexInteger
            | TokenKind::DecimalInteger
            | TokenKind::BinaryInteger
            | TokenKind::Float
            | TokenKind::String => Literal::<T>::parse(stream).map(|value| Self::Literal { value }),
            _ => Err(stream.error("Expected variable, literal, or '('")),
        }
    }

    fn parse_call(stream: &mut TokenStream<'_, impl Tokenizer>) -> Result<Self, Error> {
        let token = stream.expect_match(TokenKind::Identifier, &[])?;

        if stream.take_match(TokenKind::Symbol, &["("])?.is_none() {
            return Ok(Self::Variable { variable: token });
        };

        let mut arguments = Vec::new();
        while stream.peek_match(TokenKind::Symbol, &[")"])?.is_none() {
            let arg = Self::parse(stream)?;
            arguments.push(arg);

            if stream.take_match(TokenKind::Symbol, &[","])?.is_none() {
                break;
            }
        }
        stream.expect_match(TokenKind::Symbol, &[")"])?;

        Ok(Self::FunctionCall {
            name: token,
            arguments: arguments.into_boxed_slice(),
        })
    }
}

#[derive(Clone)]
struct TokenStream<'s, I>
where
    I: Tokenizer,
{
    source: &'s str,
    tokens: I,
}

impl<'s, I> TokenStream<'s, I>
where
    I: Tokenizer,
{
    fn new(source: &'s str, tokens: I) -> Self {
        TokenStream { source, tokens }
    }

    /// Fast-forwards the token iterator past comments.
    fn skip_comments(&mut self) -> Result<(), Error> {
        let mut peekable = self.tokens.clone();
        while let Some(token) = peekable.next() {
            if token?.kind == TokenKind::Comment {
                self.tokens = peekable.clone();
            } else {
                break;
            }
        }

        Ok(())
    }

    fn end(&mut self) -> Result<bool, Error> {
        self.skip_comments()?;

        Ok(self.tokens.clone().next().is_none())
    }

    fn peek(&mut self) -> Result<Option<Token>, Error> {
        self.skip_comments()?;

        match self.tokens.clone().next() {
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(error)) => Err(error),
            None => Ok(None),
        }
    }

    fn peek_expect(&mut self) -> Result<Token, Error> {
        self.peek()?.ok_or_else(|| Error {
            location: Location {
                start: self.source.len(),
                end: self.source.len(),
            },
            error: String::from("Unexpected end of input").into_boxed_str(),
        })
    }

    fn peek_match(
        &mut self,
        token_kind: TokenKind,
        source: &[&str],
    ) -> Result<Option<Token>, Error> {
        let Some(token) = self.peek()? else {
            return Ok(None);
        };

        let peeked = if token.kind == token_kind
            && (source.is_empty() || source.contains(&self.source(token.location)))
        {
            Some(token)
        } else {
            None
        };

        Ok(peeked)
    }

    fn take_match(
        &mut self,
        token_kind: TokenKind,
        source: &[&str],
    ) -> Result<Option<Token>, Error> {
        self.peek_match(token_kind, source).map(|token| {
            if let Some(token) = token {
                self.tokens.next();
                Some(token)
            } else {
                None
            }
        })
    }

    /// Takes the next token if it matches the expected kind and source.
    /// Returns an error if the token does not match.
    ///
    /// If `source` is empty, it only checks the token kind.
    /// If `source` is not empty, it checks if the token's source matches any of the provided strings.
    fn expect_match(&mut self, token_kind: TokenKind, source: &[&str]) -> Result<Token, Error> {
        if let Some(token) = self.take_match(token_kind, source)? {
            Ok(token)
        } else {
            let token = self.peek()?;
            let found = if let Some(token) = token {
                if token.kind == token_kind {
                    format!("found '{}'", self.source(token.location))
                } else {
                    format!("found {:?}", token.kind)
                }
            } else {
                "reached end of input".to_string()
            };
            match source {
                [] => Err(self.error(format_args!("Expected {token_kind:?}, {found}"))),
                [s] => Err(self.error(format_args!("Expected '{s}', {found}"))),
                _ => Err(self.error(format_args!("Expected one of {source:?}, {found}"))),
            }
        }
    }

    fn error(&self, message: impl Display) -> Error {
        Error {
            error: format!("Parse error: {message}").into_boxed_str(),
            location: if let Some(Ok(token)) = self.tokens.clone().next() {
                token.location
            } else {
                Location {
                    start: self.source.len(),
                    end: self.source.len(),
                }
            },
        }
    }

    fn source(&self, location: Location) -> &'s str {
        location.extract(self.source)
    }
}

pub fn parse<T>(source: &str) -> Result<Program<T>, Error>
where
    T: TypeSet,
{
    let tokens = crate::lexer::tokenize(source);
    let mut stream = TokenStream::new(source, tokens);

    Program::<T>::parse(&mut stream)
}

pub fn parse_expression<T>(source: &str) -> Result<Expression<T>, Error>
where
    T: TypeSet,
{
    let tokens = crate::lexer::tokenize(source);
    let mut stream = TokenStream::new(source, tokens);

    Expression::<T>::parse(&mut stream)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unescape() {
        assert_eq!(unescape(r#"Hello\nWorld\t!"#).unwrap(), "Hello\nWorld\t!");
        assert_eq!(unescape(r#"Hello\\World"#).unwrap(), "Hello\\World");
        assert_eq!(unescape(r#"Hello\zWorld"#), Err(6)); // Invalid escape sequence
    }

    #[test]
    fn test_out_of_range_literal() {
        let source = "0x100000000";

        let result = parse_expression::<TypeSet32>(source).expect_err("Parsing should fail");
        assert_eq!(
            "Parse error: Invalid hexadecimal integer literal",
            result.error.as_ref()
        );
    }

    #[test]
    fn test_grouped_numeric_literal() {
        let source = "1_000_000";

        let result = parse_expression::<TypeSet32>(source).unwrap();

        assert_eq!(source, result.location().extract(source));
    }

    #[test]
    fn test_parse_strings() {
        type LitVal = LiteralValue<TypeSet32>;

        let test_data = [
            (r#""hel_lo""#, Ok(LitVal::String(r#"hel_lo"#.to_string()))),
            ("1_000", Ok(LitVal::Integer(1000))),
            ("true", Ok(LitVal::Boolean(true))),
            ("false", Ok(LitVal::Boolean(false))),
            (
                "fal_se",
                Err("Parse error: Expected literal (number, string, or boolean)"),
            ),
        ];

        for (source, expected) in test_data {
            let tokens = crate::lexer::tokenize(source);
            let mut stream = TokenStream::new(source, tokens);

            let lit = match Literal::<TypeSet32>::parse(&mut stream) {
                Ok(lit) => lit,
                Err(err) => {
                    let Err(expected_err) = expected else {
                        panic!(
                            "Expected parsing to succeed, but it failed with error: {}",
                            err
                        );
                    };
                    assert_eq!(expected_err, err.to_string());
                    continue;
                }
            };

            let Ok(expected) = expected else {
                panic!("Expected error, but `{source}` was parsed successfully");
            };

            match (lit.value, expected) {
                (LitVal::Integer(a), LitVal::Integer(b)) => assert_eq!(a, b),
                (LitVal::Float(a), LitVal::Float(b)) => assert_eq!(a, b),
                (LitVal::String(a), LitVal::String(b)) => assert_eq!(a, b),
                (LitVal::Boolean(a), LitVal::Boolean(b)) => assert_eq!(a, b),
                _ => panic!("Unexpected literal type"),
            }
        }
    }
}
