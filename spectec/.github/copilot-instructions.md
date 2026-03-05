## Quick context

This repository implements SpecTec: a DSL and toolchain for the WebAssembly specification.
The codebase is OCaml/Dune-based and contains multiple backends (animation, interpreter, latex, prose, splice, etc.).

High-level layout (most relevant paths):
- `src/` : main implementation. Major subdirs: `backend-*`, `al/`, `il/`, `interpreter/`.
- `specification/` : the DSL sources for Wasm (e.g. `specification/wasm-3.0/`).
- `spectec/` : top-level tool wrapper and sample config (this is where `Makefile` lives).
- `test-*` : tests and example testbeds (e.g. `test-interpreter/sample.wast`).

## Big picture architecture (short)

- The project reads DSL spec sources in `specification/` and compiles/transforms them into different artifacts via backends under `src/backend-*`.
- Key backends:
  - `backend-animation` — produces an animated / executable DL interpreter and OCaml runner (see `src/backend-animation/interpreter-ocaml`).
  - `backend-interpreter` — reference interpreter sources and glue.
  - `backend-latex`, `backend-prose` — produce spec text and latex outputs.
- The `spectec` CLI (built by `dune`) is used to run transformations and to emit generated OCaml sources. The Makefile orchestrates common workflows.

## Developer workflows & commands

- Build the main executable and run tests:
  - From `spectec/` run `make` to build the `spectec` tool (it uses `dune` under the hood).
  - `make test` runs all test directories (each `test-*` contains its own test runner and also uses `dune runtest`).

- Run the interpreter on a `.wast` test file (example from README):
  - `spectec spec/* --interpreter test-interpreter/sample.wast`

- Generate and compile the OCaml animation/interpreter runner:
  - `make build_ocamlprog` — runs `spectec` with the flags below, generates OCaml, then builds and runs `dl_runner.exe` in `src/backend-animation/interpreter-ocaml/build`.
  - The Makefile uses `SPECTEC_FLAGS = --animate --inline --generate-ocaml "dl_codegen"` (or with `PRINT_DL=1` to also `--print-dl`).

- Quick dune commands if you prefer them directly:
  - `dune build` — build packages.
  - `dune runtest` — run tests in a package directory.

## Project-specific conventions & patterns (what an agent should know)

- DSL/rule naming: rules in the DSL have names like `rule <name>/<id>:` so backends and tests often refer to rules by `name/id` (see `src/backend-animation/def.ml` for DL representation and printing helpers).
- Generated code: the tool emits OCaml sources (used by `backend-animation`), do not edit generated files in `src/backend-animation/interpreter-ocaml/build` directly — instead adjust the generator flags or the DL source.
- Reference interpreter is copied into `src/backend-interpreter/reference-interpreter` by the Makefile: the Makefile clones `interpreter/` into that directory during `make exe` — treat that copy as generated/derived for build purposes.
- Tests: each `test-*` directory provides a Makefile-based runner and also integrates with `dune runtest`. If a test fails, the Makefile suggests `dune promote` to accept updated expectations.

## Integration points / places to look for behavior

- Spec DSL parsing & runtime: `src/al/` contains the meta-language impl (e.g. `al_util.ml`, `eval.ml`, `interpreter.ml`).
- DL AST & printer: `src/backend-animation/def.ml` and `src/backend-animation/print.ml` show how DL definitions are represented and stringified.
- Interpreter implementation(s): `interpreter/` (source reference), `src/backend-interpreter/` (integration glue), and generated OCaml runner in `src/backend-animation/interpreter-ocaml/`.
- Example specs & rules: `spec/` and `specification/wasm-3.0/` hold canonical DSL inputs.

## Helpful examples for code generation / debugging

- To produce DL and inspect it: run `./spectec spec/* --animate --inline --print-dl` from `spectec/`.
- To reproduce the OCaml-runner generation and run a sample test: `make build_ocamlprog` (it calls `./spectec $(SPEC) $(SPECTEC_FLAGS)` then `dune build` + `dune exec`).

## Pitfalls & tips

- Many subsystems are intentionally modular (multiple backends). When adding changes that affect the DL format, update all backends that consume it (`backend-*`).
- The Makefile sometimes creates temporary copies (e.g. `src/backend-interpreter/reference-interpreter`) — watch for stale copies when changing core interpreter code.
- The repo uses Dune 3.x and OCaml 5.x (see `dune-project`); prefer the opam/dune toolchain matching the README.

If anything here is unclear or you want more detail on a particular area (e.g. how to extend `backend-animation` codegen or run a particular test folder), tell me which part and I will expand or add short examples.
