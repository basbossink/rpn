use std::{cmp::min, fmt::Display};

#[derive(Clone, Copy, PartialEq, Debug)]
enum Num {
    Integer(i64),
    Float(f64, usize),
}

impl Display for Num {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Num::Integer(i) => i.fmt(f),
            Num::Float(d, prec) => {
                write!(f, "{res:.prec$e}", res = d, prec = prec - 1)
            }
        }
    }
}

enum Item {
    Operand(Num),
    Operator(BinOp),
}

struct BinOp {
    oper: Box<dyn BinaryOperator>,
}

struct Add;

impl BinaryOperator for Add {
    fn apply(&self, lhs: Num, rhs: Num) -> Num {
        match (lhs, rhs) {
            (Num::Integer(l), Num::Integer(r)) => Num::Integer(l + r),
            (Num::Float(l, prec), Num::Integer(r)) => Num::Float(l + r as f64, prec),
            (Num::Integer(l), Num::Float(r, prec)) => Num::Float(l as f64 + r, prec),
            (Num::Float(l, lprec), Num::Float(r, rprec)) => Num::Float(l + r, min(lprec, rprec)),
        }
    }
}

struct Mult;

impl BinaryOperator for Mult {
    fn apply(&self, lhs: Num, rhs: Num) -> Num {
        match (lhs, rhs) {
            (Num::Integer(l), Num::Integer(r)) => Num::Integer(l * r),
            (Num::Float(l, prec), Num::Integer(r)) => Num::Float(l * r as f64, prec),
            (Num::Integer(l), Num::Float(r, prec)) => Num::Float(l as f64 * r, prec),
            (Num::Float(l, lprec), Num::Float(r, rprec)) => Num::Float(l * r, min(lprec, rprec)),
        }
    }
}

struct Div;
impl BinaryOperator for Div {
    fn apply(&self, lhs: Num, rhs: Num) -> Num {
        match (lhs, rhs) {
            (Num::Integer(l), Num::Integer(r)) => Num::Integer(l / r),
            (Num::Float(l, prec), Num::Integer(r)) => Num::Float(l / r as f64, prec),
            (Num::Integer(l), Num::Float(r, prec)) => Num::Float(l as f64 / r, prec),
            (Num::Float(l, lprec), Num::Float(r, rprec)) => Num::Float(l / r, min(lprec, rprec)),
        }
    }
}

trait BinaryOperator {
    fn apply(&self, lhs: Num, rhs: Num) -> Num;
}

fn main() {
    println!("Hello, world!");
}

fn process_input(input: Vec<Item>) -> Result<Num, &'static str> {
    let mut stack: Vec<Num> = Vec::new();
    for item in input.iter() {
        match item {
            Item::Operator(bin_op) => match stack.pop() {
                Some(rhs) => match stack.pop() {
                    Some(lhs) => {
                        stack.push(bin_op.oper.apply(lhs, rhs));
                        Ok(())
                    }
                    _ => Err("expecting one more operand on the stack"),
                },
                _ => Err("expecting two more operands on the stack"),
            },
            Item::Operand(num) => {
                stack.push(*num);
                Ok(())
            }
        }?;
    }
    stack.pop().ok_or("stack empty at bend of input")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_support_integer_addition() {
        let input = vec![
            Item::Operand(Num::Integer(1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(BinOp {
                oper: Box::new(Add),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(3), result)
    }

    #[test]
    fn should_support_float_and_integer_addition() {
        let input = vec![
            Item::Operand(Num::Float(1.0, 1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(BinOp {
                oper: Box::new(Add),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(3.0, 1), result)
    }

    #[test]
    fn should_support_multiple_integer_additions_in_a_row() {
        let input = vec![
            Item::Operand(Num::Integer(1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(BinOp {
                oper: Box::new(Add),
            }),
            Item::Operand(Num::Integer(1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(BinOp {
                oper: Box::new(Add),
            }),
            Item::Operator(BinOp {
                oper: Box::new(Add),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(6), result)
    }

    #[test]
    fn should_support_integer_multiplication() {
        let input = vec![
            Item::Operand(Num::Integer(2)),
            Item::Operand(Num::Integer(3)),
            Item::Operator(BinOp {
                oper: Box::new(Mult),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(6), result)
    }

    #[test]
    fn should_support_integer_and_float_multiplication() {
        let input = vec![
            Item::Operand(Num::Integer(2)),
            Item::Operand(Num::Float(3.5, 1)),
            Item::Operator(BinOp {
                oper: Box::new(Mult),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(7.0, 1), result)
    }

    #[test]
    fn should_support_integer_division() {
        let input = vec![
            Item::Operand(Num::Integer(5)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(BinOp {
                oper: Box::new(Div),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(2), result)
    }

    #[test]
    fn should_support_integer_and_float_division() {
        let input = vec![
            Item::Operand(Num::Float(5.0, 1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(BinOp {
                oper: Box::new(Div),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(2.5, 1), result)
    }

    #[test]
    fn should_support_track_significant_digits() {
        let input = vec![
            Item::Operand(Num::Float(5.00, 2)),
            Item::Operand(Num::Float(2.0, 1)),
            Item::Operator(BinOp {
                oper: Box::new(Div),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(2.5, 1), result)
    }

    #[test]
    fn should_format_with_significant_digits() {
        let f = Num::Float(1000.0, 2);
        let result = format!("{f}");
        assert_eq!("1.0e3", &result);
    }
}
