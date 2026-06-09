# Tiny ML Compiler

Tiny ML is a simplified version of Standard ML, a functional programming language. This project implements a compiler that translates Tiny ML programs into machine code for Mach, an abstract machine written in OCaml.

This project was developed as part of the POSTECH CSED321: Programming Languages course. I extended the original project by independently implementing Hindley-Milner type inference engine, which was originally provided as a pre-compiled binary.

For detailed information about this project, please refer to the assignment specifications: [hw7.pdf](/docs/hw7.pdf) and [mach.pdf](/docs/mach.pdf).

## Key Features

- Supports closures, higher-order and polymorphic functions, recursive functions, recursive datatypes, and pattern matching.
- Implements Hindley-Milner type inference based on Algorithm W.

## Sample TML Program

```sml
datatype list = Nil | Cons of (int * list);

val rec append =
  fn Nil => (fn x => Cons (x, Nil))
   | Cons (h, t) => (fn x => Cons (h, append t x));

val rec reverse =
  fn Nil => Nil
   | Cons (h, t) => append (reverse t) h;

val l = Cons (1, Cons (2, Nil));

reverse l;;
```

Note that every TML program is also a valid SML program. You can test any SML program in your web browser at [sosml.org](https://sosml.org).

## Build

Required OCaml version: `4.14.3`
