use crate::{lexer::Token, parser::TypeSet, Location};

#[derive(Debug)]
pub struct Program<T>
where
    T: TypeSet,
{
    pub items: Vec<Item<T>>,
}

#[derive(Debug)]
pub enum Item<T>
where
    T: TypeSet,
{
    Function(Function<T>),
    ExternFunction(ExternalFunction),
    GlobalVariable(GlobalVariable<T>),
}

#[derive(Debug)]
pub struct GlobalVariable<T>
where
    T: TypeSet,
{
    pub decl_token: Token,
    pub identifier: Token,
    pub colon: Token,
    pub type_token: TypeHint,
    pub equals_token: Token,
    pub initializer: Expression<T>,
    pub semicolon: Token,
}
impl<T> GlobalVariable<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        let start = self.decl_token.location.start;
        let end = self.semicolon.location.end;
        Location { start, end }
    }
}

#[derive(Debug)]
pub struct ReturnDecl {
    pub return_token: Token,
    pub return_type: TypeHint,
}

#[derive(Debug)]
pub struct ExternalFunction {
    pub extern_fn_token: Token,
    pub fn_token: Token,
    pub name: Token,
    pub opening_paren: Token,
    pub arguments: Vec<FunctionArgument>,
    pub closing_paren: Token,
    pub return_decl: Option<ReturnDecl>,
    pub semicolon: Token,
}

#[derive(Debug)]
pub struct Function<T>
where
    T: TypeSet,
{
    pub fn_token: Token,
    pub name: Token,
    pub opening_paren: Token,
    pub arguments: Vec<FunctionArgument>,
    pub closing_paren: Token,
    pub return_decl: Option<ReturnDecl>,
    pub body: Body<T>,
}

#[derive(Debug)]
pub struct Body<T>
where
    T: TypeSet,
{
    pub opening_brace: Token,
    pub statements: Vec<Statement<T>>,
    pub closing_brace: Token,
}
impl<T: TypeSet> Body<T> {
    pub fn location(&self) -> Location {
        Location {
            start: self.opening_brace.location.start,
            end: self.closing_brace.location.end,
        }
    }
}

impl<T> Clone for Body<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        Self {
            opening_brace: self.opening_brace,
            statements: self.statements.clone(),
            closing_brace: self.closing_brace,
        }
    }
}

#[derive(Debug)]
pub struct FunctionArgument {
    pub name: Token,
    pub colon: Token,
    pub reference_token: Option<Token>,
    pub arg_type: TypeHint,
}

#[derive(Clone, Copy, Debug)]
pub struct TypeHint {
    pub type_name: Token,
}

#[derive(Debug)]
pub struct VariableDefinition<T>
where
    T: TypeSet,
{
    pub decl_token: Token,
    pub identifier: Token,
    pub type_token: Option<TypeHint>,
    pub equals_token: Token,
    pub initializer: RightHandExpression<T>,
    pub semicolon: Token,
}

impl<T> Clone for VariableDefinition<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        Self {
            decl_token: self.decl_token,
            identifier: self.identifier,
            type_token: self.type_token,
            equals_token: self.equals_token,
            initializer: self.initializer.clone(),
            semicolon: self.semicolon,
        }
    }
}

impl<T> VariableDefinition<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        let start = self.decl_token.location.start;
        let end = self.semicolon.location.end;
        Location { start, end }
    }
}

#[derive(Debug)]
pub struct ReturnWithValue<T>
where
    T: TypeSet,
{
    pub return_token: Token,
    pub expression: RightHandExpression<T>,
    pub semicolon: Token,
}

impl<T> Clone for ReturnWithValue<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        Self {
            return_token: self.return_token,
            expression: self.expression.clone(),
            semicolon: self.semicolon,
        }
    }
}

impl<T> ReturnWithValue<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        let start = self.return_token.location.start;
        let end = self.semicolon.location.end;
        Location { start, end }
    }
}

#[derive(Debug, Clone)]
pub struct EmptyReturn {
    pub return_token: Token,
    pub semicolon: Token,
}

impl EmptyReturn {
    pub fn location(&self) -> Location {
        let start = self.return_token.location.start;
        let end = self.semicolon.location.end;
        Location { start, end }
    }
}

#[derive(Debug)]
pub struct If<T>
where
    T: TypeSet,
{
    pub if_token: Token,
    pub condition: RightHandExpression<T>,
    pub body: Body<T>,
    pub else_branch: Option<Else<T>>,
}
impl<T> If<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        Location {
            start: self.if_token.location.start,
            end: self
                .else_branch
                .as_ref()
                .map(|else_branch| else_branch.location().end)
                .unwrap_or_else(|| self.body.location().end),
        }
    }
}

impl<T> Clone for If<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        Self {
            if_token: self.if_token,
            condition: self.condition.clone(),
            body: self.body.clone(),
            else_branch: self.else_branch.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Loop<T>
where
    T: TypeSet,
{
    pub loop_token: Token,
    pub body: Body<T>,
}
impl<T> Loop<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        Location {
            start: self.loop_token.location.start,
            end: self.body.location().end,
        }
    }
}

impl<T> Clone for Loop<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        Self {
            loop_token: self.loop_token,
            body: self.body.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Break {
    pub break_token: Token,
    pub semicolon: Token,
}

impl Break {
    pub fn location(&self) -> Location {
        let start = self.break_token.location.start;
        let end = self.semicolon.location.end;
        Location { start, end }
    }
}

#[derive(Debug, Clone)]
pub struct Continue {
    pub continue_token: Token,
    pub semicolon: Token,
}

impl Continue {
    pub fn location(&self) -> Location {
        let start = self.continue_token.location.start;
        let end = self.semicolon.location.end;
        Location { start, end }
    }
}

#[derive(Debug)]
pub enum Statement<T>
where
    T: TypeSet,
{
    VariableDefinition(VariableDefinition<T>),
    Return(ReturnWithValue<T>),
    EmptyReturn(EmptyReturn),
    If(If<T>),
    Loop(Loop<T>),
    Break(Break),
    Continue(Continue),
    Scope(Body<T>),
    Expression {
        expression: Expression<T>,
        semicolon: Token,
    },
    ImplicitReturn(RightHandExpression<T>),
}
impl<T: TypeSet> Statement<T> {
    pub fn location(&self) -> Location {
        match self {
            Statement::VariableDefinition(variable_definition) => variable_definition.location(),
            Statement::Return(return_with_value) => return_with_value.location(),
            Statement::EmptyReturn(empty_return) => empty_return.location(),
            Statement::If(if_stmt) => if_stmt.location(),
            Statement::Loop(loop_stmt) => loop_stmt.location(),
            Statement::Break(break_stmt) => break_stmt.location(),
            Statement::Continue(continue_stmt) => continue_stmt.location(),
            Statement::Scope(body) => body.location(),
            Statement::Expression {
                expression,
                semicolon,
            } => Location {
                start: expression.location().start,
                end: semicolon.location.end,
            },
            Statement::ImplicitReturn(right_hand_expression) => right_hand_expression.location(),
        }
    }
}

impl<T> Clone for Statement<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        match self {
            Self::VariableDefinition(arg0) => Self::VariableDefinition(arg0.clone()),
            Self::Return(arg0) => Self::Return(arg0.clone()),
            Self::EmptyReturn(arg0) => Self::EmptyReturn(arg0.clone()),
            Self::If(arg0) => Self::If(arg0.clone()),
            Self::Loop(arg0) => Self::Loop(arg0.clone()),
            Self::Break(arg0) => Self::Break(arg0.clone()),
            Self::Continue(arg0) => Self::Continue(arg0.clone()),
            Self::Scope(body) => Self::Scope(body.clone()),
            Self::Expression {
                expression,
                semicolon,
            } => Self::Expression {
                expression: expression.clone(),
                semicolon: *semicolon,
            },
            Statement::ImplicitReturn(expression) => Self::ImplicitReturn(expression.clone()),
        }
    }
}

#[derive(Debug)]
pub struct Else<T>
where
    T: TypeSet,
{
    pub else_token: Token,
    pub else_body: Body<T>,
}
impl<T> Else<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        Location {
            start: self.else_token.location.start,
            end: self.else_body.location().end,
        }
    }
}

impl<T> Clone for Else<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        Self {
            else_token: self.else_token,
            else_body: self.else_body.clone(),
        }
    }
}

#[derive(Debug)]
pub enum Expression<T>
where
    T: TypeSet,
{
    Assignment {
        left_expr: LeftHandExpression,
        operator: Token,
        right_expr: RightHandExpression<T>,
    },
    Expression {
        expression: RightHandExpression<T>,
    },
}
impl<T> Clone for Expression<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        match self {
            Expression::Assignment {
                left_expr,
                operator,
                right_expr,
            } => Self::Assignment {
                left_expr: *left_expr,
                operator: *operator,
                right_expr: right_expr.clone(),
            },
            Expression::Expression { expression } => Self::Expression {
                expression: expression.clone(),
            },
        }
    }
}
impl<T> Expression<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        match self {
            Expression::Expression { expression } => expression.location(),
            Expression::Assignment {
                left_expr,
                operator: _,
                right_expr,
            } => {
                let mut location = left_expr.location();

                location.start = location.start.min(right_expr.location().start);
                location.end = location.end.max(right_expr.location().end);

                location
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum LeftHandExpression {
    Name { variable: Token },
    Deref { operator: Token, name: Token },
}

impl LeftHandExpression {
    pub fn location(&self) -> Location {
        match self {
            LeftHandExpression::Name { variable } => variable.location,
            LeftHandExpression::Deref { operator, name } => {
                let mut location = operator.location;

                location.start = location.start.min(name.location.start);
                location.end = location.end.max(name.location.end);

                location
            }
        }
    }
}

#[derive(Debug)]
pub enum RightHandExpression<T>
where
    T: TypeSet,
{
    Variable {
        variable: Token,
    },
    Literal {
        value: Literal<T>,
    },
    UnaryOperator {
        name: Token,
        operand: Box<Self>,
    },
    BinaryOperator {
        name: Token,
        operands: Box<[Self; 2]>,
    },
    FunctionCall {
        name: Token,
        arguments: Box<[Self]>,
    },
}

impl<T> Clone for RightHandExpression<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        match self {
            Self::Variable { variable } => Self::Variable {
                variable: *variable,
            },
            Self::Literal { value } => Self::Literal {
                value: value.clone(),
            },
            Self::UnaryOperator { name, operand } => Self::UnaryOperator {
                name: *name,
                operand: operand.clone(),
            },
            Self::BinaryOperator { name, operands } => Self::BinaryOperator {
                name: *name,
                operands: operands.clone(),
            },
            Self::FunctionCall { name, arguments } => Self::FunctionCall {
                name: *name,
                arguments: arguments.clone(),
            },
        }
    }
}
impl<T> RightHandExpression<T>
where
    T: TypeSet,
{
    pub fn location(&self) -> Location {
        match self {
            RightHandExpression::Variable { variable } => variable.location,
            RightHandExpression::Literal { value } => value.location,
            RightHandExpression::FunctionCall { name, arguments } => {
                let mut location = name.location;
                for arg in arguments {
                    location.start = location.start.min(arg.location().start);
                    location.end = location.end.max(arg.location().end);
                }
                location
            }
            RightHandExpression::UnaryOperator { name, operand: rhs } => {
                let mut location = name.location;

                location.start = location.start.min(rhs.location().start);
                location.end = location.end.max(rhs.location().end);

                location
            }
            RightHandExpression::BinaryOperator {
                name,
                operands: arguments,
            } => {
                let mut location = name.location;
                for arg in arguments.iter() {
                    location.start = location.start.min(arg.location().start);
                    location.end = location.end.max(arg.location().end);
                }
                location
            }
        }
    }
}

#[derive(Debug)]
pub struct Literal<T>
where
    T: TypeSet,
{
    pub value: LiteralValue<T>,
    pub location: Location,
}

impl<T> Clone for Literal<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            location: self.location,
        }
    }
}

#[derive(Debug)]
pub enum LiteralValue<T>
where
    T: TypeSet,
{
    Integer(T::Integer),
    Float(T::Float),
    String(String),
    Boolean(bool),
}

impl<T> Clone for LiteralValue<T>
where
    T: TypeSet,
{
    fn clone(&self) -> Self {
        match self {
            Self::Integer(arg0) => Self::Integer(*arg0),
            Self::Float(arg0) => Self::Float(*arg0),
            Self::String(arg0) => Self::String(arg0.clone()),
            Self::Boolean(arg0) => Self::Boolean(*arg0),
        }
    }
}
