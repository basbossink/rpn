# rpn

<img alt="License: BSD-2-clause" src="https://img.shields.io/badge/license-BSD--2--clause-green" />

A command-line reverse polish notation calculator.

### Installation

#### Windows/Linux/Mac

If you are either on Windows, Linux or Mac, the preferred way of installing is downloading the appropriate archive for your operating system from the [Releases section](https://github.com/basbossink/rpn/releases) and unpacking it somewhere on your system. Note that the archives do *NOT* contain a top level directory. After that just ensure that `rpn` is on your `$PATH`.

#### Build from source

A working [Rust](https://www.rust-lang.org/) development environment is required to install this calculator. If needed follow the [installation instructions](https://www.rust-lang.org/tools/install) for your platform.

```
git clone https://github.com/basbossink/rpn.git
cargo install rpn --path rpn
```

### Why could this be helpful

There are a great number of excellent calculator applications available this toy is merely for the simplest of calculations. The only distinguishing feature is that the syntax of the calculator does not use any character that has a special meaning in the shell. This means you can just type the calculation as a set of parameters to the calculator without the need to quote it. The calculator also uses at most the number of significant digits that was used in the input.

### Usage

```
rpn [-v|--version] [-d|--debug] [numbers/operators]...
```

#### Examples

```sh
$ rpn 2 3 x
6
$ rpn 2 3 +
5
$ rpn 2 3 4 x +
14
$ rpn 1.234 1.2341 +
2.468e0
$ rpn 3 6 .. .+ # add the numbers 3 4 5
12
$ rpn 3 6 .. .x # multiply the numbers 3 4 5
60
$ rpn 37 s # calculate the square of 37 (37*37)
1369
$ rpn 37 r # calculate the square root of 37
6.08276e0
$ rpn 5 ! # calculate 5 factorial
120
$ rpn pi 0.15 s # pi is a predefined constant (π), calculate the surface of a cicle with radius 0.15
2.25e-2
```

To see the version information use the `-v` or `--version` flag. If you get unexpected results the `-d` or `--debug` flag can be used as the first parameter, this prints out the intermediary steps.

#### Supported operators

| Token | Description | Example |
|-- |-- | -- |
|`+`| addition | `-2 3 + # => 1`|
|`-`| subtraction| `3 2 - # => 1`|
|`x`| multiplication | `2 3 x # => 6` |
|`xx`| exponentiation | `2 3 xx # => 8`|
|`/`| division | `2 3 / # => 0; 3.0 2 / # =>  1.5`|
|`b`| binomial coefficient | `6 3 b # => 20; 6!/(3!*(6-3)!)`|
|`s`| square | `3 s # => 9`|
|`r`| square root | `4 r # => 2`|
|`!`| factorial | `3 ! # => 6`|
|`.+`| summation | `2 3 4 .+ # => 9`|
|`.x`| product | `2 3 4 .x # => 24`|
|`..`| put range excluding end on the stack | `2 5 .. .+ # => 9`|
|`..=`| put range including end on the stack | `2 5 ..= .+ # => 14`|
|`pi`| predefined constant π | ` 2 pi 0.54 .x # => 3.39e0`|

### License

This project is licensed under the BSD-2-clause license.

***
Readme made with 💖 using [README Generator by Dhravya Shah](https://github.com/Dhravya/readme-generator)
