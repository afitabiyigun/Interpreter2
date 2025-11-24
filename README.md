# interp2 – A Small OCaml Subset Interpreter

This project implements an interpreter for a small, explicitly typed subset of OCaml, including desugaring, static type checking, and big-step evaluation.

## Overview

The interpreter supports:

- **Desugaring** from a surface language with multi-argument functions and top-level `let` bindings into a core expression language.
- **Type checking** with an explicit typing context, function types, and detailed error reporting for ill-typed programs.
- **Big-step evaluation** with environments, closures (including recursion), arithmetic and boolean operators, conditionals, and `assert`.
- A top-level `interp` function that composes parsing, type checking, and evaluation, and a CLI wrapper to run programs from files.

The language is a subset of OCaml with:

- Base types: `int`, `bool`, `unit`
- Function types: `τ1 -> τ2`
- Expressions: literals, variables, `if … then … else …`, `let` / `let rec`, anonymous functions, application, and `assert`
- Operators: `+ - * / mod < <= > >= = <> && ||`

## Project Structure

```text
bin/
  interp2.ml      # main entry point that wires up CLI to the library
lib/
  dune            # library build config
  utils.ml        # shared types (AST, types, values, errors, etc.)
  lexer.mll       # lexer for the surface language
  parser.mly      # parser for the surface language
  interp2.ml      # implementation of desugar, type_of, eval, interp
test/
  ...             # optional test files / sample programs
dune-project
interp2.opam
spec.pdf          # assignment spec / formal semantics (for reference)
