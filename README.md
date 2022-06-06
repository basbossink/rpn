# rpn

<img alt="License: BSD-2-clause" src="https://img.shields.io/badge/license-BSD--2--clause-green" />
A command-line reverse polish notation calculator.

### Installation

A working [Rust](https://www.rust-lang.org/) development environment is required to install this calculator. If needed follow the [installation instructions](https://www.rust-lang.org/tools/install) for your platform.

```
git clone https://github.com/basbossink/rpn.git
cargo install rpn --path rpn
```

### Why could this be helpful

There are a great number of excellent calculator applications available this toy is merely for the simplest of calculations. The only distinguishing feature is that the syntax of the calculator does not use any character that has a special meaning in the shell. This means you can just type the calculation as a set of parameters to the calculator without the need to quote it. The calculator also uses at most the number of significant digits that was used in the input.

### Usage

```sh
$ rpn 2 3 x 
6
$ rpn 2 3 +
5
$ rpn 2 3 4 x +
14
$ rpn 1.234 1.2341 +
2.468e0
```

#### Supported operators

| Token | Description | Example |
|-- |-- | -- |
|`+`| addition | `-2 3 + # => 1`| 
|`-`| subtraction| `3 2 - # => 1`| 
|`x`| multiplication | `2 3 x # => 6` |
|`xx`| exponentiation | `2 3 xx # => 8`| 
|`/`| division | `2 3 / # => 0; 3.0 2 / # =>  1.5`| 
|`s`| square | `3 s # => 9`| 
|`r`| square root | `4 r # => 2`| 
|`!`| factorial | `3 ! # => 6`| 
|`.+`| summation | `2 3 4 .+ # => 9`| 
|`.x`| product | `2 3 4 .x # => 24`| 
|`..`| put range excluding end on the stack | `2 5 .. .+ # => 9`| 
|`..=`| put range including end on the stack | `2 5 .. .+ # => 14`| 

### License

This project is licensed under the BSD-2-clause license

***
Readme made with 💖 using [README Generator by Dhravya Shah](https://github.com/Dhravya/readme-generator)
