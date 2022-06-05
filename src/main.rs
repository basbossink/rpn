use lazy_static::lazy_static;
use regex::Regex;
use std::{
    cmp::min,
    fmt::{Display, Write},
    str::FromStr,
};

lazy_static! {
    static ref INT_REGEX: Regex = Regex::new(r"^-?[1-9]\d*$").unwrap();
    static ref BIN_OPS: Vec<&'static str> = vec!["+", "-", "x", "xx", "/"];
}

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

impl FromStr for Num {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if INT_REGEX.is_match(s) {
            s.parse::<i64>().map_or_else(
                |err| Err(format!("could not parse integer number '{s}'; {err}")),
                |i| Ok(Num::Integer(i)),
            )
        } else {
            let prec = s
                .chars()
                .take_while(|c| *c != 'e' || *c != 'E')
                .filter(|c| char::is_digit(*c, 10))
                .count();
            s.parse::<f64>().map_or_else(
                |err| {
                    Err(format!(
                        "could not parse floating point number '{s}'; {err}"
                    ))
                },
                |f| Ok(Num::Float(f, prec)),
            )
        }
    }
}

enum Item {
    Operand(Num),
    Operator(BinOp),
}

impl FromStr for Item {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<Num>().map_or_else(
            |err_1| s.parse::<BinOp>().map_or_else(
            |err_2| Err(format!("could not parse '{s}' as either a number or operator; {err_1}; {err_2}")),
            |o| Ok(Item::Operator(o))),
            |n| Ok(Item::Operand(n)))
    }
}
struct BinOp {
    oper: Box<dyn BinaryOperator>,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.oper)
    }
}

impl FromStr for BinOp {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(BinOp {
                oper: Box::new(Add),
            }),
            "-" => Ok(BinOp {
                oper: Box::new(Sub),
            }),
            "x" => Ok(BinOp {
                oper: Box::new(Mult),
            }),
            "xx" => Ok(BinOp {
                oper: Box::new(Pow),
            }),
            "/" => Ok(BinOp {
                oper: Box::new(Div),
            }),
            bad => Err(format!("not a valid operator '{bad}'")),
        }
    }
}

macro_rules! impl_bin_op {
    ($oper:ident, $native_op:path) => {
        impl BinaryOperator for $oper {
            fn apply(&self, lhs: Num, rhs: Num) -> Num {
                match (lhs, rhs) {
                    (Num::Integer(l), Num::Integer(r)) => Num::Integer($native_op(l, r)),
                    (Num::Float(l, prec), Num::Integer(r)) => {
                        Num::Float($native_op(l, r as f64), prec)
                    }
                    (Num::Integer(l), Num::Float(r, prec)) => {
                        Num::Float($native_op(l as f64, r), prec)
                    }
                    (Num::Float(l, lprec), Num::Float(r, rprec)) => {
                        Num::Float($native_op(l, r), min(lprec, rprec))
                    }
                }
            }
        }
    };
}

macro_rules! impl_display {
    ($oper:ident, $repr: literal) => {
        impl Display for $oper {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", $repr)
            }
        }
    };
}

struct Add;
struct Mult;
struct Div;
struct Sub;
struct Pow;

impl_display!(Add, "+");
impl_display!(Sub, "-");
impl_display!(Mult, "x");
impl_display!(Div, "/");
impl_display!(Pow, "xx");

impl_bin_op!(Add, std::ops::Add::add);
impl_bin_op!(Sub, std::ops::Sub::sub);
impl_bin_op!(Mult, std::ops::Mul::mul);
impl_bin_op!(Div, std::ops::Div::div);

impl BinaryOperator for Pow {
    fn apply(&self, lhs: Num, rhs: Num) -> Num {
        match (lhs, rhs) {
            (Num::Integer(l), Num::Integer(r)) => Num::Integer(l.pow(r as u32)),
            (Num::Float(l, prec), Num::Integer(r)) => Num::Float(l.powf(r as f64), prec),
            (Num::Integer(l), Num::Float(r, prec)) => Num::Float((l as f64).powf(r), prec),
            (Num::Float(l, lprec), Num::Float(r, rprec)) => {
                Num::Float(l.powf(r), min(lprec, rprec))
            }
        }
    }
}

trait BinaryOperator: Display {
    fn apply(&self, lhs: Num, rhs: Num) -> Num;
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

fn main() -> Result<(), String> {
    let (numbers, errors): (Vec<_>, Vec<_>) = std::env::args()
        .into_iter()
        .skip(1)
        .flat_map(move |s| {
            s.split_whitespace()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
        })
        .map(|s| s.parse::<Item>())
        .partition(Result::is_ok);
    if !errors.is_empty() {
        let mut joined = String::new();
        errors.into_iter().map(|e| e.err().unwrap()).for_each(|e| {
            writeln!(joined, "{}", e).ok();
        });
        Err(joined)
    } else {
        let good_ones = numbers.into_iter().map(|i| i.ok().unwrap()).collect();
        let result = process_input(good_ones)?;
        println!("{result}");
        Ok(())
    }
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
    fn should_support_integer_power_of() {
        let input = vec![
            Item::Operand(Num::Integer(2)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(BinOp {
                oper: Box::new(Pow),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(4), result)
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
    fn should_support_float_and_integer_power_of() {
        let input = vec![
            Item::Operand(Num::Integer(4)),
            Item::Operand(Num::Float(0.5, 1)),
            Item::Operator(BinOp {
                oper: Box::new(Pow),
            }),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(2.0, 1), result)
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

    #[test]
    fn should_parse_integer() {
        let expected = Num::Integer(37);
        let actual: Num = "37".parse().unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn should_parse_float() {
        let expected = Num::Float(37.0, 3);
        let actual: Num = "37.0".parse().unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn should_parse_and_unparse_operator() {
        let expected = String::from("+");
        let actual = format!("{}", "+".parse::<BinOp>().unwrap());
        assert_eq!(expected, actual);
    }
}
