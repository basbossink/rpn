// Copyright (C) 2022 by Bas Bossink
use std::{cmp::min, fmt::Display, str::FromStr};

const DEFAULT_PRECISION: usize = 6;
const PI: Num = Num::Float(std::f64::consts::PI, 37);
const PI_TOKEN: &str = "pi";

#[derive(Clone, Copy, Debug)]
enum Num {
    Integer(i64),
    Float(f64, usize),
}

impl PartialEq for Num {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(lhs), Self::Integer(rhs)) => lhs == rhs,
            (Self::Integer(_), Self::Float(_, _)) => false,
            (Self::Float(_, _), Self::Integer(_)) => false,
            (Self::Float(ref lhs, ref lhs_prec), Self::Float(ref rhs, ref rhs_prec)) => {
                let min_prec = 0.max(lhs_prec.min(rhs_prec) - 1) as i32;
                let bound = 0.5_f64 * 10.0_f64.powi(-1 * min_prec);
                let abs_diff = (lhs - rhs).abs();
                (lhs == rhs && lhs_prec == rhs_prec) || abs_diff < bound
            }
        }
    }
}

impl Display for Num {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Integer(i) => i.fmt(f),
            Self::Float(d, prec) if -10.0_f64 < d && d < 10.0_f64 => {
                write!(f, "{res:.prec$}", res = d, prec = prec - 1)
            }
            Self::Float(d, prec) => {
                write!(f, "{res:.prec$e}", res = d, prec = prec - 1)
            }
        }
    }
}

impl FromStr for Num {
    type Err = RpnError;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        if PI_TOKEN == s {
            return Ok(PI);
        }
        s.parse::<i64>().map_or_else(
                |err_1| {
            let prec = s
                .chars()
                .take_while(|c| *c != 'e' || *c != 'E')
                .filter(|c| char::is_digit(*c, 10))
                .count();
            s.parse::<f64>().map_or_else(
                |err_2| {
                    Err(Self::Err::Syntax(format!(
                        "could not parse as floating point or integer number '{s}';\n\t\t\t- {err_1};\n\t\t\t- {err_2}"
                    )))
                },
                |f| Ok(Self::Float(f, prec)),
            )
                },
                |i| Ok(Self::Integer(i)),
            )
    }
}

enum Item {
    Operand(Num),
    Operator(Oper),
}

impl FromStr for Item {
    type Err = RpnError;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        s.parse::<Num>().map_or_else(
            |err_1| s.parse::<Oper>().map_or_else(
            |err_2| Err(Self::Err::Syntax(format!("could not parse '{s}' as either a number or operator;\n\t\t- {};\n\t\t- {}", err_1.msg(), err_2.msg()))),
            |o| Ok(Self::Operator(o))),
            |n| Ok(Self::Operand(n)))
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
    type Err = RpnError;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        match s {
            "+" => Ok(Self::Bin(BinOp {
                oper: Box::new(Add),
            })),
            "-" => Ok(Self::Bin(BinOp {
                oper: Box::new(Sub),
            })),
            "x" => Ok(Self::Bin(BinOp {
                oper: Box::new(Mult),
            })),
            "xx" => Ok(Self::Bin(BinOp {
                oper: Box::new(Pow),
            })),
            "/" => Ok(Self::Bin(BinOp {
                oper: Box::new(Div),
            })),
            "b" => Ok(Self::Bin(BinOp {
                oper: Box::new(Binomial),
            })),
            "s" => Ok(Self::Unary(UnOp {
                oper: Box::new(Square),
            })),
            "r" => Ok(Self::Unary(UnOp {
                oper: Box::new(Sqrt),
            })),
            "!" => Ok(Self::Unary(UnOp {
                oper: Box::new(Factorial),
            })),
            ".+" => Ok(Self::Nary(NAryOp {
                oper: Box::new(NAdd),
            })),
            ".x" => Ok(Self::Nary(NAryOp {
                oper: Box::new(NMult),
            })),
            ".." => Ok(Self::Range(RangeOp {
                oper: Box::new(RangeEx),
            })),
            "..=" => Ok(Self::Range(RangeOp {
                oper: Box::new(RangeInc),
            })),
            bad => Err(Self::Err::Syntax(format!("not a valid operator '{bad}'"))),
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
    fn apply(&self, nums: std::vec::IntoIter<Num>) -> Num;
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

struct Binomial;
impl_display!(Binomial, "b");

impl BinaryOperator for Binomial {
    fn apply(&self, lhs: Num, rhs: Num) -> Num {
        match (lhs, rhs) {
            (Num::Integer(l), Num::Integer(r)) if r <= l => Num::Integer(binom(l, r)),
            _ => Num::Float(f64::NAN, DEFAULT_PRECISION),
        }
    }
}

fn binom(n: i64, k: i64) -> i64 {
    let numer: i64 = ((n - (k - 1))..=n).product();
    let denom = fact(k);
    numer / denom
}

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

const fn fact(n: i64) -> i64 {
    let mut result = 1;
    let mut counter = 1;
    while counter <= n {
        result *= counter;
        counter += 1;
    }
    result
}

struct Mult;
impl_display!(Mult, "x");
impl_bin_op!(Mult, std::ops::Mul::mul);

struct NAdd;
impl_display!(NAdd, ".+");

impl NAryOperator for NAdd {
    fn apply(&self, nums: std::vec::IntoIter<Num>) -> Num {
        let adder = Add;
        nums.into_iter()
            .fold(Num::Integer(0), |acc, num| adder.apply(acc, num))
    }
}

struct NMult;
impl_display!(NMult, ".x");

impl NAryOperator for NMult {
    fn apply(&self, nums: std::vec::IntoIter<Num>) -> Num {
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
            Num::Float(f, prec) => Num::Float(f.sqrt(), prec),
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

#[derive(Debug)]
enum RpnError {
    Syntax(String),
    Stack(String),
    Io(std::io::Error),
}

impl RpnError {
    fn msg(self) -> String {
        match self {
            Self::Syntax(s) => s,
            Self::Stack(s) => s,
            Self::Io(e) => e.to_string(),
        }
    }
}

type Result<T> = std::result::Result<T, RpnError>;

impl Display for RpnError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Syntax(s) => write!(f, "syntax error: {s}"),
            Self::Stack(s) => write!(f, "stack error: {s}"),
            Self::Io(e) => write!(f, "io error: {e:?}"),
        }
    }
}

impl From<std::io::Error> for RpnError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

fn get_two_operands(stack: &mut Vec<Num>) -> Result<(Num, Num)> {
    let rhs = get_operand(stack)?;
    let lhs = get_operand(stack)?;
    Ok((lhs, rhs))
}

fn get_operand(stack: &mut Vec<Num>) -> Result<Num> {
    stack
        .pop()
        .ok_or_else(|| RpnError::Stack("expecting one more operand on the stack".to_owned()))
}

fn process_input(
    input: &[Item],
    print_debug: bool,
    mut stdout: impl std::io::Write,
) -> Result<Num> {
    let mut stack: Vec<Num> = Vec::new();
    for item in input {
        match *item {
            Item::Operator(Oper::Bin(BinOp { oper: ref bin_op })) => {
                let (lhs, rhs) = get_two_operands(&mut stack)?;
                let result = bin_op.apply(lhs, rhs);
                if print_debug {
                    stdout.write_fmt(format_args!("{lhs} {bin_op} {rhs} = {result}\n"))?;
                }
                stack.push(result);
                Ok::<(), RpnError>(())
            }
            Item::Operator(Oper::Unary(UnOp { oper: ref un_op })) => {
                let num = get_operand(&mut stack)?;
                let result = un_op.apply(num);
                if print_debug {
                    stdout.write_fmt(format_args!("{num} {un_op} = {result}\n"))?;
                }
                stack.push(result);
                Ok(())
            }
            Item::Operator(Oper::Nary(NAryOp { oper: ref nary_op })) => {
                let result = nary_op.apply(stack.into_iter());
                if print_debug {
                    stdout.write_fmt(format_args!("... {nary_op} = {result}\n"))?;
                }
                stack = vec![result];
                Ok(())
            }
            Item::Operator(Oper::Range(RangeOp { oper: ref range_op })) => {
                let (lhs, rhs) = get_two_operands(&mut stack)?;
                if print_debug {
                    stdout.write_fmt(format_args!(
                        "putting range {lhs} {range_op} {rhs} on the stack\n"
                    ))?;
                }
                let result = range_op.apply(lhs, rhs);
                result.into_iter().for_each(|i| stack.push(i));
                Ok(())
            }
            Item::Operand(ref num) => {
                stack.push(*num);
                if print_debug {
                    stdout.write_fmt(format_args!(
                        "putting {num} on the stack; new stack {:?}\n",
                        stack
                    ))?;
                }
                Ok(())
            }
        }?;
    }
    stack
        .pop()
        .ok_or_else(|| RpnError::Stack("stack empty at end of input".to_owned()))
}

fn process_arguments(
    args: Vec<String>,
    print_debug: bool,
    stdout: &mut impl std::io::Write,
) -> Result<Num> {
    let (numbers, errors): (Vec<_>, Vec<_>) = args
        .into_iter()
        .map(|s| s.parse::<Item>())
        .partition(Result::is_ok);
    if errors.is_empty() {
        let good_ones: Vec<_> = numbers.into_iter().map(|i| i.ok().unwrap()).collect();
        process_input(&good_ones, print_debug, stdout)
    } else {
        let joined = errors
            .into_iter()
            .map(|e| e.err().unwrap().msg())
            .collect::<Vec<String>>()
            .join(";\n\t- ");
        Err(RpnError::Syntax(format!("\n\t- {joined}")))
    }
}

fn split_all_args_on_whitespace<I>(iterable: I) -> Vec<String>
where
    I: IntoIterator<Item = String>,
{
    iterable
        .into_iter()
        .skip(1)
        .flat_map(move |s| {
            s.split_whitespace()
                .map(std::borrow::ToOwned::to_owned)
                .collect::<Vec<String>>()
        })
        .collect()
}

fn print_version(mut stdout: impl std::io::Write) -> Result<()> {
    let version = env!("CARGO_PKG_VERSION");
    let name = env!("CARGO_PKG_NAME");
    let authors = env!("CARGO_PKG_AUTHORS");
    let repository = env!("CARGO_PKG_REPOSITORY");
    stdout.write_fmt(format_args!(
        r#"{name} {version}.
Copyright (C) 2022 {authors}.
License: BSD 2-Clause "Simplified" License. <https://github.com/basbossink/rpn/raw/main/LICENSE>.
Home: <{repository}>.
"#
    ))?;
    stdout.flush()?;
    Ok(())
}

fn main() {
    let args = std::env::args();
    let mut stdout = std::io::stdout().lock();
    let result = rpn(args, &mut stdout);
    if let Err(e) = result {
        eprintln!("{e}");
        std::process::exit(-1);
    }
}

fn rpn<I>(args: I, stdout: &mut impl std::io::Write) -> Result<()>
where
    I: IntoIterator<Item = String>,
{
    let splitted = split_all_args_on_whitespace(args);
    if splitted.iter().any(|s| s == "-v" || s == "--version") {
        print_version(stdout)?;
        return Ok(());
    }
    let (debug, rest): (Vec<_>, Vec<_>) = splitted
        .into_iter()
        .partition(|st| *st == "-d" || *st == "--debug");
    let print_debug = !debug.is_empty();
    let num = process_arguments(rest, print_debug, stdout)?;
    stdout.write_fmt(format_args!("{num}\n"))?;
    stdout.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    mod num {
        use super::*;

        #[test]
        fn equals_should_take_precision_into_account() {
            let lhs = Num::Float(1.1, 2);
            let rhs = Num::Float(1.0, 2);
            assert_ne!(lhs, rhs);
        }

        #[test]
        fn equals_should_take_precision_into_account_upto_precision() {
            let lhs = Num::Float(1.0, 2);
            let rhs = Num::Float(1.01, 2);
            assert_eq!(lhs, rhs);

            let lhs = Num::Float(1.0, 1);
            let rhs = Num::Float(1.06, 1);
            assert_eq!(lhs, rhs);
        }

        #[test]
        fn equals_should_take_precision_into_account_upto_precision_round_up() {
            let lhs = Num::Float(1.0, 2);
            let rhs = Num::Float(1.06, 2);
            assert_ne!(lhs, rhs);
        }
    }

    fn act_assert(input: &[Item], expected: Num) {
        let result = process_input(&input, false, Vec::new()).unwrap();
        assert_eq!(expected, result)
    }

    #[test]
    fn should_support_integer_addition() {
        act_assert(
            &[
                Item::Operand(Num::Integer(1)),
                Item::Operand(Num::Integer(2)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Add),
                })),
            ],
            Num::Integer(3),
        );
    }

    #[test]
    fn should_support_integer_squaring() {
        act_assert(
            &[
                Item::Operand(Num::Integer(2)),
                Item::Operator(Oper::Unary(UnOp {
                    oper: Box::new(Square),
                })),
            ],
            Num::Integer(4),
        );
    }

    #[test]
    fn should_support_square_root() {
        act_assert(
            &[
                Item::Operand(Num::Integer(4)),
                Item::Operator(Oper::Unary(UnOp {
                    oper: Box::new(Sqrt),
                })),
            ],
            Num::Float(2.0, DEFAULT_PRECISION),
        );
    }

    #[test]
    fn should_support_integer_power_of() {
        act_assert(
            &[
                Item::Operand(Num::Integer(2)),
                Item::Operand(Num::Integer(2)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Pow),
                })),
            ],
            Num::Integer(4),
        );
    }

    #[test]
    fn should_support_float_and_integer_addition() {
        act_assert(
            &[
                Item::Operand(Num::Float(1.0, 1)),
                Item::Operand(Num::Integer(2)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Add),
                })),
            ],
            Num::Float(3.0, 1),
        );
    }

    #[test]
    fn should_support_float_and_integer_power_of() {
        act_assert(
            &[
                Item::Operand(Num::Integer(4)),
                Item::Operand(Num::Float(0.5, 1)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Pow),
                })),
            ],
            Num::Float(2.0, 1),
        );
    }

    #[test]
    fn should_support_multiple_integer_additions_in_a_row() {
        act_assert(
            &[
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
            ],
            Num::Integer(6),
        );
    }

    #[test]
    fn should_support_integer_multiplication() {
        act_assert(
            &[
                Item::Operand(Num::Integer(2)),
                Item::Operand(Num::Integer(3)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Mult),
                })),
            ],
            Num::Integer(6),
        );
    }

    #[test]
    fn should_support_integer_and_float_multiplication() {
        act_assert(
            &[
                Item::Operand(Num::Integer(2)),
                Item::Operand(Num::Float(3.5, 1)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Mult),
                })),
            ],
            Num::Float(7.0, 1),
        );
    }

    #[test]
    fn should_support_integer_division() {
        act_assert(
            &[
                Item::Operand(Num::Integer(5)),
                Item::Operand(Num::Integer(2)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Div),
                })),
            ],
            Num::Integer(2),
        );
    }

    #[test]
    fn should_support_integer_and_float_division() {
        act_assert(
            &[
                Item::Operand(Num::Float(5.0, 1)),
                Item::Operand(Num::Integer(2)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Div),
                })),
            ],
            Num::Float(2.5, 1),
        );
    }

    #[test]
    fn should_support_track_significant_digits() {
        act_assert(
            &[
                Item::Operand(Num::Float(5.00, 2)),
                Item::Operand(Num::Float(2.0, 1)),
                Item::Operator(Oper::Bin(BinOp {
                    oper: Box::new(Div),
                })),
            ],
            Num::Float(2.5, 1),
        );
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
        let input = [
            Item::Operand(Num::Float(1.234, 4)),
            Item::Operand(Num::Float(10.2341, 6)),
            Item::Operator(Oper::Bin(BinOp {
                oper: Box::new(Add),
            })),
        ];
        let result = format!("{}", process_input(&input, false, Vec::new()).unwrap());
        assert_eq!("1.147e1", result)
    }

    mod process_arguments {
        use super::*;

        fn test_process_arguments(args: Vec<&str>, expected: Num) {
            let input = args.into_iter().map(String::from).collect();
            let mut buf = Vec::new();
            let actual = process_arguments(input, false, &mut buf).unwrap();
            assert_eq!(expected, actual);
        }

        #[test]
        fn should_support_addition() {
            test_process_arguments(vec!["1", "2", "+"], Num::Integer(3));
        }

        #[test]
        fn should_support_subtraction() {
            test_process_arguments(vec!["1", "2", "-"], Num::Integer(-1));
        }

        #[test]
        fn should_support_multiplication() {
            test_process_arguments(vec!["4", "2", "x"], Num::Integer(8));
        }

        #[test]
        fn should_support_division() {
            test_process_arguments(vec!["4", "2", "/"], Num::Integer(2));
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
        fn should_support_square_int() {
            test_process_arguments(vec!["3", "s"], Num::Integer(9));
        }

        #[test]
        fn should_support_square_float() {
            test_process_arguments(vec!["1.50", "s"], Num::Float(2.25, 3));
        }

        #[test]
        fn should_support_sqrt_int() {
            test_process_arguments(vec!["9", "r"], Num::Float(3.0, DEFAULT_PRECISION));
        }

        #[test]
        fn should_support_sqrt_float() {
            test_process_arguments(vec!["2.0", "r"], Num::Float(1.41, 2));
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

        #[test]
        fn should_support_combinations() {
            test_process_arguments(vec!["6", "3", "b"], Num::Integer(20));
        }

        #[test]
        fn should_support_power() {
            test_process_arguments(vec!["6", "3", "xx"], Num::Integer(216));
        }

        #[test]
        fn should_support_power_float_exponent() {
            test_process_arguments(vec!["9", "0.5", "xx"], Num::Float(3.0, 2));
        }

        #[test]
        fn should_support_power_float_base_float_exponent() {
            test_process_arguments(vec!["9.0", "0.5", "xx"], Num::Float(3.0, 2));
        }

        #[test]
        fn should_support_power_float_base_integer_exponent() {
            test_process_arguments(vec!["3.0", "2", "xx"], Num::Float(9.0, 2));
        }

        #[test]
        fn should_support_pi() {
            test_process_arguments(vec!["pi", "pi", "/"], Num::Float(1.0, 37));
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

    mod rpn {
        use super::*;

        fn run_case(args: &[&'static str]) -> (Result<()>, String) {
            let mut buf = Vec::new();
            let mut args: Vec<String> = args.iter().map(|s| s.to_string()).collect();
            args.insert(0, "rpn".to_owned());
            let actual = rpn(args, &mut buf);
            let written = String::from_utf8(buf).unwrap();
            (actual, written)
        }

        #[test]
        fn should_accept_long_version_flag() {
            let (res, written) = run_case(&["--version"]);
            assert!(
                written.contains("rpn"),
                "expected version string to contain rpn but got: {written}"
            );
            assert!(res.is_ok());
        }

        #[test]
        fn should_accept_short_version_flag() {
            let (res, written) = run_case(&["-v"]);
            assert!(
                written.contains("rpn"),
                "expected version string to contain rpn but got: {written}"
            );
            assert!(res.is_ok());
        }

        #[test]
        fn should_accept_short_debug_flag() {
            let (res, written) = run_case(&["-d", "2 3 +"]);
            assert!(
                written.contains("2 + 3 = 5"),
                "expected debug output to contain 2 + 3 = 5 but got: {written}"
            );
            assert!(res.is_ok());
        }

        #[test]
        fn should_accept_long_debug_flag() {
            let (res, written) = run_case(&["--debug", "2 3 +"]);
            assert!(
                written.contains("2 + 3 = 5"),
                "expected debug output to contain 2 + 3 = 5 but got: {written}"
            );
            assert!(res.is_ok());
        }

        #[test]
        fn should_report_syntax_error() {
            let (res, _) = run_case(&["2a 3 +"]);
            let msg = res
                .err()
                .expect("syntax error should be decteted")
                .to_string();
            assert!(
                msg.contains("2a"),
                "expected parse error to contain 2a but got: [{msg}]"
            );
        }

        #[test]
        fn should_report_stack_error() {
            let (res, _) = run_case(&["2 +"]);
            let msg = res
                .err()
                .expect("stack error should be detected")
                .to_string();
            assert!(
                msg.contains("stack"),
                "expected stack error to contain stack error but got: [{msg}]"
            );
        }

        #[test]
        fn should_report_stack_error_with_no_args() {
            let (res, _) = run_case(&[]);
            let msg = res
                .err()
                .expect("stack error should be detected")
                .to_string();
            assert!(
                msg.contains("stack"),
                "expected stack error to contain stack error but got: [{msg}]"
            );
        }

        #[test]
        fn should_allow_string_containing_whitespace() {
            let (res, written) = run_case(&["2 2", " 3 .x"]);
            assert!(res.is_ok());
            assert_eq!(written, "12\n");
        }

        #[test]
        fn should_process_arguments() {
            let (res, written) = run_case(&["2.37", "2", "xx"]);
            assert!(res.is_ok());
            assert_eq!(written, "5.62\n");
        }
    }
}
