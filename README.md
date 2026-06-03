# Tiny ML Compiler

Tiny ML is a simplified version of Standard ML, a functional programming language.  
This project implements a compiler that translates Tiny ML programs into machine code for Mach, an abstract machine written in OCaml.

### Key Features:

- Supports closures, higher-order and polymorphic functions, recursive functions, recursive datatypes, and pattern matching.
- Implements Hindley-Milner type inference based on Algorithm W.

This project was developed as part of the POSTECH CSED321: Programming Languages course. I extended the original project by independently implementing Hindley-Milner type inference engine, which was originally provided as a pre-compiled binary.

For detailed information about this project, please refer to the assignment specifications: [hw7.pdf](/docs/hw7.pdf) and [mach.pdf](/docs/mach.pdf).

