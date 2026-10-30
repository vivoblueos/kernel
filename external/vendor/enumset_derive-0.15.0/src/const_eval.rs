use crate::error;
use syn::spanned::Spanned;
use syn::{BinOp, Expr, ExprBinary, Lit, UnOp};

pub fn eval_literal(expr: &Expr) -> syn::Result<i64> {
    match expr {
        Expr::Binary(binary) => match binary.op {
            BinOp::Add(_) => eval_bin(binary, |a, b| a.checked_add(b)),
            BinOp::Sub(_) => eval_bin(binary, |a, b| a.checked_sub(b)),
            BinOp::Mul(_) => eval_bin(binary, |a, b| a.checked_mul(b)),
            BinOp::Div(_) => eval_bin(binary, |a, b| a.checked_div(b)),
            BinOp::Rem(_) => eval_bin(binary, |a, b| a.checked_rem(b)),
            BinOp::BitXor(_) => eval_bin(binary, |a, b| Some(a ^ b)),
            BinOp::BitAnd(_) => eval_bin(binary, |a, b| Some(a & b)),
            BinOp::BitOr(_) => eval_bin(binary, |a, b| Some(a | b)),
            BinOp::Shl(_) => eval_bin(binary, |a, b| a.checked_shl(b.try_into().ok()?)),
            BinOp::Shr(_) => eval_bin(binary, |a, b| a.checked_shr(b.try_into().ok()?)),
            _ => error(expr.span(), "Expression not supported by enumset.")?,
        },
        Expr::Group(group) => eval_literal(&group.expr),
        Expr::Lit(lit) => match &lit.lit {
            Lit::Int(lit_int) => match lit_int.base10_parse::<i64>() {
                Ok(val) => Ok(val),
                Err(_) => error(expr.span(), "Enum discriminants must fit into `isize`.")?,
            },
            Lit::Byte(lit_byte) => Ok(lit_byte.value() as i64),
            _ => error(expr.span(), "Expression not supported by enumset.")?,
        },
        Expr::Paren(paren) => eval_literal(&paren.expr),
        Expr::Unary(unary) => match unary.op {
            UnOp::Not(_) => Ok(!eval_literal(&unary.expr)?),
            UnOp::Neg(_) => Ok(-eval_literal(&unary.expr)?),
            _ => error(expr.span(), "Expression not supported by enumset.")?,
        },
        _ => error(expr.span(), "Expression not supported by enumset.")?,
    }
}

fn eval_bin(binary: &ExprBinary, op: impl FnOnce(i64, i64) -> Option<i64>) -> syn::Result<i64> {
    let result = op(eval_literal(&binary.left)?, eval_literal(&binary.right)?);
    match result {
        None => error(binary.span(), "Error while evaluating discriminant."),
        Some(x) => Ok(x),
    }
}
