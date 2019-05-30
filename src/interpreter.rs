use crate::error::InterpreterError;
use crate::error::InterpreterErrorKind;
use crate::parser::Ast;
use crate::parser::BinOp;
use crate::parser::UniOp;

pub struct Interpreter;

impl Interpreter {
    pub fn new() -> Self {
        Interpreter
    }
}

impl Interpreter {
    pub fn eval(&mut self, expr: &Ast) -> Result<i64, InterpreterError> {
        use crate::parser::AstKind::*;
        match expr.value {
            Num(i) => Ok(i as i64),
            UniOp { ref op, ref e } => {
                let e = self.eval(e)?;
                Ok(self.eval_uniop(op, e))
            }
            BinOp {
                ref op,
                ref l,
                ref r,
            } => {
                let l = self.eval(l)?;
                let r = self.eval(r)?;
                self.eval_binop(op, l, r)
                    .map_err(|e| InterpreterError::new(e, expr.loc.clone()))
            }
        }
    }

    fn eval_uniop(&mut self, op: &UniOp, n: i64) -> i64 {
        use crate::parser::UniOpKind::*;
        match op.value {
            Plus => n,
            Minus => -n,
        }
    }

    fn eval_binop(&mut self, op: &BinOp, l: i64, r: i64) -> Result<i64, InterpreterErrorKind> {
        use crate::parser::BinOpKind::*;
        match op.value {
            Add => Ok(l + r),
            Sub => Ok(l - r),
            Mult => Ok(l * r),
            Div => {
                if r == 0 {
                    Err(InterpreterErrorKind::DivisionByZero)
                } else {
                    Ok(l / r)
                }
            }
        }
    }
}
