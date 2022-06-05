use std::{cmp::min, fmt::Display, str::FromStr, vec::Drain};

const DEFAULT_PRECISION: usize = 6;

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
        s.parse::<i64>().map_or_else(
                |err_1| {
            let prec = s
                .chars()
                .take_while(|c| *c != 'e' || *c != 'E')
                .filter(|c| char::is_digit(*c, 10))
                .count();
            s.parse::<f64>().map_or_else(
                |err_2| {
                    Err(format!(
                        "could not parse as floating point or integer number '{s}'; {err_1}; {err_2}"
                    ))
                },
                |f| Ok(Num::Float(f, prec)),
            )
                },
                |i| Ok(Num::Integer(i)),
            )
    }
}

enum Item {
    Operand(Num),
    Operator(Oper),
}

enum Oper {
    Bin(BinOp),
    Unary(UnOp),
    Nary(NAryOp),
}

impl Display for Oper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bin(b) => b.fmt(f),
            Self::Unary(u) => u.fmt(f),
            Self::Nary(n) => n.fmt(f),
        }
    }
}

impl FromStr for Item {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<Num>().map_or_else(
            |err_1| s.parse::<Oper>().map_or_else(
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

struct UnOp {
    oper: Box<dyn UnaryOperator>,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.oper)
    }
}

struct NAryOp {
    oper: Box<dyn NAryOperator>,
}

impl Display for NAryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.oper)
    }
}

impl FromStr for Oper {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
            "-" => Ok(Oper::Bin(BinOp {
                oper: Box::new(Sub),
            })),
            "x" => Ok(Oper::Bin(BinOp {
                oper: Box::new(Mult),
            })),
            "xx" => Ok(Oper::Bin(BinOp {
                oper: Box::new(Pow),
            })),
            "/" => Ok(Oper::Bin(BinOp {
                oper: Box::new(Div),
            })),
            "s" => Ok(Oper::Unary(UnOp {
                oper: Box::new(Square),
            })),
            "r" => Ok(Oper::Unary(UnOp {
                oper: Box::new(Sqrt),
            })),
            "!" => Ok(Oper::Unary(UnOp {
                oper: Box::new(Factorial),
            })),
            ".+" => Ok(Oper::Nary(NAryOp {
                oper: Box::new(NAdd),
            })),
            ".x" => Ok(Oper::Nary(NAryOp {
                oper: Box::new(NMult),
            })),
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
struct Square;
struct Sqrt;
struct NAdd;
struct NMult;
struct Factorial;

impl_display!(Add, "+");
impl_display!(Sub, "-");
impl_display!(Mult, "x");
impl_display!(Div, "/");
impl_display!(Pow, "xx");
impl_display!(Sqrt, "r");
impl_display!(Square, "s");
impl_display!(NAdd, ".+");
impl_display!(NMult, ".x");
impl_display!(Factorial, "!");

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

impl UnaryOperator for Square {
    fn apply(&self, num: Num) -> Num {
        match num {
            Num::Integer(i) => Num::Integer(i * i),
            Num::Float(f, prec) => Num::Float(f * f, prec),
        }
    }
}

impl UnaryOperator for Sqrt {
    fn apply(&self, num: Num) -> Num {
        match num {
            Num::Integer(i) => Num::Float((i as f64).sqrt(), DEFAULT_PRECISION),
            Num::Float(f, prec) => Num::Float(f * f, prec),
        }
    }
}

impl UnaryOperator for Factorial {
    fn apply(&self, num: Num) -> Num {
        match num {
            Num::Integer(i) if i >= 0 => Num::Integer(fact(i)),
            Num::Integer(_) => Num::Float(f64::NAN, DEFAULT_PRECISION),
            Num::Float(_, prec) => Num::Float(f64::NAN, prec),
        }
    }
}

fn fact(n: i64) -> i64 {
    let mut result = 1;
    let mut counter = 1;
    while counter <= n {
        result = result * counter;
        counter = counter + 1;
    }
    result
}

trait BinaryOperator: Display {
    fn apply(&self, lhs: Num, rhs: Num) -> Num;
}

trait UnaryOperator: Display {
    fn apply(&self, num: Num) -> Num;
}

trait NAryOperator: Display {
    fn apply(&self, nums: Drain<Num>) -> Num;
}

impl NAryOperator for NAdd {
    fn apply(&self, nums: Drain<Num>) -> Num {
        let adder = Add;
        nums.into_iter()
            .fold(Num::Integer(0), |acc, num| adder.apply(acc, num))
    }
}

impl NAryOperator for NMult {
    fn apply(&self, nums: Drain<Num>) -> Num {
        let multiplication = Mult;
        nums.into_iter()
            .fold(Num::Integer(1), |acc, num| multiplication.apply(acc, num))
    }
}

fn process_input(input: Vec<Item>) -> Result<Num, &'static str> {
    let mut stack: Vec<Num> = Vec::new();
    for item in input.iter() {
        match item {
            Item::Operator(Oper::Bin(BinOp { oper: bin_op })) => match stack.pop() {
                Some(rhs) => match stack.pop() {
                    Some(lhs) => {
                        stack.push(bin_op.apply(lhs, rhs));
                        Ok(())
                    }
                    _ => Err("expecting one more operand on the stack"),
                },
                _ => Err("expecting two more operands on the stack"),
            },
            Item::Operator(Oper::Unary(UnOp { oper: un_op })) => match stack.pop() {
                Some(num) => {
                    stack.push(un_op.apply(num));
                    Ok(())
                }
                _ => Err("expecting one more operand on the stack"),
            },
            Item::Operator(Oper::Nary(NAryOp { oper: nary_op })) => {
                let result = nary_op.apply(stack.drain(..));
                stack = vec![result];
                Ok(())
            }
            Item::Operand(num) => {
                stack.push(*num);
                Ok(())
            }
        }?;
    }
    stack.pop().ok_or("stack empty at end of input")
}

fn process_arguments(args: Vec<String>) -> Result<Num, String> {
    let (numbers, errors): (Vec<_>, Vec<_>) = args
        .into_iter()
        .map(|s| s.parse::<Item>())
        .partition(Result::is_ok);
    if !errors.is_empty() {
        let joined = errors
            .into_iter()
            .map(|e| e.err().unwrap())
            .collect::<Vec<String>>()
            .join(";");
        Err(joined)
    } else {
        let good_ones = numbers.into_iter().map(|i| i.ok().unwrap()).collect();
        process_input(good_ones).map_err(String::from)
    }
}

fn main() -> Result<(), String> {
    let splitted = std::env::args()
        .into_iter()
        .skip(1)
        .flat_map(move |s| {
            s.split_whitespace()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
        })
        .collect();
    let result = process_arguments(splitted);
    match result {
        Ok(num) => {
            println!("{num}");
            Ok(())
        }
        Err(err) => Err(err),
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
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(3), result)
    }

    #[test]
    fn should_support_integer_squaring() {
        let input = vec![
            Item::Operand(Num::Integer(2)),
            Item::Operator(Oper::Unary(UnOp {
                oper: Box::new(Square),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(4), result)
    }

    #[test]
    fn should_support_square_root() {
        let input = vec![
            Item::Operand(Num::Integer(4)),
            Item::Operator(Oper::Unary(UnOp {
                oper: Box::new(Sqrt),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(2.0, DEFAULT_PRECISION), result)
    }

    #[test]
    fn should_support_integer_power_of() {
        let input = vec![
            Item::Operand(Num::Integer(2)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Pow),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(4), result)
    }

    #[test]
    fn should_support_float_and_integer_addition() {
        let input = vec![
            Item::Operand(Num::Float(1.0, 1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(3.0, 1), result)
    }

    #[test]
    fn should_support_float_and_integer_power_of() {
        let input = vec![
            Item::Operand(Num::Integer(4)),
            Item::Operand(Num::Float(0.5, 1)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Pow),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(2.0, 1), result)
    }

    #[test]
    fn should_support_multiple_integer_additions_in_a_row() {
        let input = vec![
            Item::Operand(Num::Integer(1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
            Item::Operand(Num::Integer(1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(6), result)
    }

    #[test]
    fn should_support_integer_multiplication() {
        let input = vec![
            Item::Operand(Num::Integer(2)),
            Item::Operand(Num::Integer(3)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Mult),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(6), result)
    }

    #[test]
    fn should_support_integer_and_float_multiplication() {
        let input = vec![
            Item::Operand(Num::Integer(2)),
            Item::Operand(Num::Float(3.5, 1)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Mult),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(7.0, 1), result)
    }

    #[test]
    fn should_support_integer_division() {
        let input = vec![
            Item::Operand(Num::Integer(5)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Div),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Integer(2), result)
    }

    #[test]
    fn should_support_integer_and_float_division() {
        let input = vec![
            Item::Operand(Num::Float(5.0, 1)),
            Item::Operand(Num::Integer(2)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Div),
            })),
        ];
        let result = process_input(input).unwrap();
        assert_eq!(Num::Float(2.5, 1), result)
    }

    #[test]
    fn should_support_track_significant_digits() {
        let input = vec![
            Item::Operand(Num::Float(5.00, 2)),
            Item::Operand(Num::Float(2.0, 1)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Div),
            })),
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
        let actual = format!("{}", "+".parse::<Oper>().unwrap());
        assert_eq!(expected, actual);
    }

    mod process_arguments {
        use super::*;

        fn test_process_arguments(args: Vec<&str>, expected: Num) {
            let input = args.into_iter().map(String::from).collect();
            let actual = process_arguments(input).unwrap();
            assert_eq!(expected, actual);
        }

        #[test]
        fn should_apply_nary_plus() {
            test_process_arguments(vec!["1", "2", "3", ".+", "1", "+"], Num::Integer(7));
        }

        #[test]
        fn should_apply_nary_mult() {
            test_process_arguments(vec!["1", "2.0", "3.5", ".x", "1", "+"], Num::Float(8.0, 2));
        }

        #[test]
        fn should_support_square_and_sqrt() {
            test_process_arguments(
                vec!["3", "s", "4", "s", "+", "r"],
                Num::Float(5.0, DEFAULT_PRECISION),
            );
        }

        #[test]
        fn should_support_factorial() {
            test_process_arguments(vec!["3", "!", "4", "+"], Num::Integer(10));
        }
    }

    mod fact_should_be_correct_for {
        use super::*;

        macro_rules! fact_test_case {
            ($name:ident, $input:literal, $expected:literal) => {
                #[test]
                fn $name() {
                    assert_eq!($expected, fact($input));
                }
            };
        }

        fact_test_case!(one, 1, 1);
        fact_test_case!(two, 2, 2);
        fact_test_case!(three, 3, 6);
        fact_test_case!(five, 5, 120);
        fact_test_case!(ten, 10, 3628800);
    }
}
