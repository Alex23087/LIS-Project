# FAILURE Analyzer
**FAILURE Analyzer** is a tool for static analysis and bug detection which implements *Separation Sufficient Incorrectness Logic* as the base logic on which the analysis is driven, as described in this [paper](https://arxiv.org/pdf/2310.18156).

## Building, Running, Installing

### Dependencies
- [OCaml](https://ocaml.org/) - OCaml Version 4.14
- [OPAM](https://opam.ocaml.org/) - OCaml Package Manager
- [Dune](https://dune.build/) - build system
- [SymAlg](https://github.com/jrk/symalg) - symbolic algebra library.

### Installing the dependencies
- `bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"`
- `opam init`
- `opam update`
- `opam install dune ppx_deriving odoc ppx_inline_test menhirLib sexplib menhir`
- `git submodule update --init --recursive`

### Building and running
- `make build`
- `dune exec lisproject`

### Testing
- `make test`
- `make test-rerun` To force running all the tests (even cached ones)

### Documentation
- `make doc` To only build the documentation
- `make docopen` To build and then open the documentation in browser
- The built documentation can be found at `./_build/default/_doc/_html/index.html`

### Install build
- `make install`
- The executable and the generated documentation can be found at `./_install`

### Troubleshooting
-   Dune not found after successful installation
    ```
    make build
    make: dune: No such file or directory
    ```
    solution: `eval $(opam env)`

## Trivia
**FAILURE** is an italian achronim for **F**orse **A**lessandro **S**i **L**a**URE**a, which translates to "Alessandro maybe graduates", a running joke between the developers of the tool.