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

enum Oper {
    Bin(BinOp),
    Unary(UnOp),
    Nary(NAryOp),
    Range(RangeOp),
}

impl Display for Oper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bin(b) => b.fmt(f),
            Self::Unary(u) => u.fmt(f),
            Self::Nary(n) => n.fmt(f),
            Self::Range(r) => r.fmt(f),
        }
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
            ".." => Ok(Oper::Range(RangeOp {
                oper: Box::new(RangeEx),
            })),
            "..=" => Ok(Oper::Range(RangeOp {
                oper: Box::new(RangeInc),
            })),
            bad => Err(format!("not a valid operator '{bad}'")),
        }
    }
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

trait RangeOperator: Display {
    fn apply(&self, lhs: Num, rhs: Num) -> Vec<Num>;
}

macro_rules! impl_disp_oper {
    ($target:ident, $member:ident) => {
        impl Display for $target {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.$member)
            }
        }
    };
}

struct BinOp {
    oper: Box<dyn BinaryOperator>,
}
impl_disp_oper!(BinOp, oper);

struct NAryOp {
    oper: Box<dyn NAryOperator>,
}
impl_disp_oper!(NAryOp, oper);

struct RangeOp {
    oper: Box<dyn RangeOperator>,
}

impl_disp_oper!(RangeOp, oper);

struct UnOp {
    oper: Box<dyn UnaryOperator>,
}
impl_disp_oper!(UnOp, oper);

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
impl_display!(Add, "+");
impl_bin_op!(Add, std::ops::Add::add);

struct Div;
impl_display!(Div, "/");
impl_bin_op!(Div, std::ops::Div::div);

struct Factorial;
impl_display!(Factorial, "!");

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

struct Mult;
impl_display!(Mult, "x");
impl_bin_op!(Mult, std::ops::Mul::mul);

struct NAdd;
impl_display!(NAdd, ".+");

impl NAryOperator for NAdd {
    fn apply(&self, nums: Drain<Num>) -> Num {
        let adder = Add;
        nums.into_iter()
            .fold(Num::Integer(0), |acc, num| adder.apply(acc, num))
    }
}

struct NMult;
impl_display!(NMult, ".x");

impl NAryOperator for NMult {
    fn apply(&self, nums: Drain<Num>) -> Num {
        let multiplication = Mult;
        nums.into_iter()
            .fold(Num::Integer(1), |acc, num| multiplication.apply(acc, num))
    }
}

struct Pow;
impl_display!(Pow, "xx");

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

struct RangeEx;
impl_display!(RangeEx, "..");

impl RangeOperator for RangeEx {
    fn apply(&self, lhs: Num, rhs: Num) -> Vec<Num> {
        match (lhs, rhs) {
            (Num::Integer(l), Num::Integer(r)) => (l..r).into_iter().map(Num::Integer).collect(),
            _ => Vec::new(),
        }
    }
}

struct RangeInc;
impl_display!(RangeInc, "..=");

impl RangeOperator for RangeInc {
    fn apply(&self, lhs: Num, rhs: Num) -> Vec<Num> {
        match (lhs, rhs) {
            (Num::Integer(l), Num::Integer(r)) => (l..=r).into_iter().map(Num::Integer).collect(),
            _ => Vec::new(),
        }
    }
}

struct Sqrt;
impl_display!(Sqrt, "r");

impl UnaryOperator for Sqrt {
    fn apply(&self, num: Num) -> Num {
        match num {
            Num::Integer(i) => Num::Float((i as f64).sqrt(), DEFAULT_PRECISION),
            Num::Float(f, prec) => Num::Float(f * f, prec),
        }
    }
}

struct Square;
impl_display!(Square, "s");

impl UnaryOperator for Square {
    fn apply(&self, num: Num) -> Num {
        match num {
            Num::Integer(i) => Num::Integer(i * i),
            Num::Float(f, prec) => Num::Float(f * f, prec),
        }
    }
}

struct Sub;
impl_display!(Sub, "-");
impl_bin_op!(Sub, std::ops::Sub::sub);

fn get_two_operands(stack: &mut Vec<Num>) -> Result<(Num, Num), &'static str> {
    let rhs = get_operand(stack)?;
    let lhs = get_operand(stack)?;
    Ok((lhs, rhs))
}

fn get_operand(stack: &mut Vec<Num>) -> Result<Num, &'static str> {
    stack.pop().ok_or("expecting one more operand on the stack")
}

fn process_input(input: Vec<Item>, print_debug: bool) -> Result<Num, &'static str> {
    let mut stack: Vec<Num> = Vec::new();
    for item in input.iter() {
        match item {
            Item::Operator(Oper::Bin(BinOp { oper: bin_op })) => {
                let (lhs, rhs) = get_two_operands(&mut stack)?;
                let result = bin_op.apply(lhs, rhs);
                if print_debug {
                    println!("{lhs} {bin_op} {rhs} = {result}");
                }
                stack.push(result);
                Ok(())
            }
            Item::Operator(Oper::Unary(UnOp { oper: un_op })) => {
                let num = get_operand(&mut stack)?;
                let result = un_op.apply(num);
                if print_debug {
                    println!("{num} {un_op} = {result}");
                }
                stack.push(result);
                Ok(())
            }
            Item::Operator(Oper::Nary(NAryOp { oper: nary_op })) => {
                let result = nary_op.apply(stack.drain(..));
                if print_debug {
                    println!("... {nary_op} = {result}");
                }
                stack = vec![result];
                Ok(())
            }
            Item::Operator(Oper::Range(RangeOp { oper: range_op })) => {
                let (lhs, rhs) = get_two_operands(&mut stack)?;
                if print_debug {
                    println!("putting range {lhs} {range_op} {rhs} on the stack");
                }
                let result = range_op.apply(lhs, rhs);
                result.into_iter().for_each(|i| stack.push(i));
                Ok(())
            }
            Item::Operand(num) => {
                stack.push(*num);
                if print_debug {
                    println!("putting {num} on the stack; new stack {:?}", stack);
                }
                Ok(())
            }
        }?;
    }
    stack.pop().ok_or("stack empty at end of input")
}

fn process_arguments(args: Vec<String>, print_debug: bool) -> Result<Num, String> {
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
        process_input(good_ones, print_debug).map_err(String::from)
    }
}

fn split_all_args_on_whitespace() -> Vec<String> {
    std::env::args()
        .into_iter()
        .skip(1)
        .flat_map(move |s| {
            s.split_whitespace()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
        })
        .collect()
}

fn print_version() {
    let version = env!("CARGO_PKG_VERSION");
    let name = env!("CARGO_PKG_NAME");
    let authors = env!("CARGO_PKG_AUTHORS");
    let copyright_year = env!("COPYRIGHT_YEAR");
    let hash = env!("GIT_COMMIT_SHORT_HASH");
    let repository = env!("CARGO_PKG_REPOSITORY");
    println!(
        r#"{name} {version} {hash}.
Copyright (C) {copyright_year} {authors}.
License BSD 2-Clause "Simplified" License. <https://github.com/basbossink/rpn/raw/main/LICENSE>.
Home: <{repository}>.
"#
    )
}

fn main() -> Result<(), String> {
    let splitted = split_all_args_on_whitespace();
    if splitted.iter().any(|s| s == "-v" || s == "--version") {
        print_version();
        return Ok(());
    }
    let (debug, rest): (Vec<_>, Vec<_>) = splitted
        .into_iter()
        .partition(|st| *st == "-d" || *st == "--debug");
    let print_debug = debug.len() > 0;
    let result = process_arguments(rest, print_debug);
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

    #[test]
    fn should_round_to_significant_digit() {
        let input = vec![
            Item::Operand(Num::Float(1.234, 4)),
            Item::Operand(Num::Float(1.2341, 5)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
        ];
        let result = format!("{}", process_input(input).unwrap());
        assert_eq!("2.468e0", result)
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

        #[test]
        fn should_support_range() {
            test_process_arguments(vec!["1", "5", "..", ".+"], Num::Integer(10));
        }

        #[test]
        fn should_support_inclusive_range() {
            test_process_arguments(vec!["1", "5", "..=", ".+"], Num::Integer(15));
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
