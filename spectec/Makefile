# Configuration

NAME = spectec
EXT = $(NAME)
LOG = _log
PRINT_DL ?= 0
UNDEP ?= 0

# Main targets

.PHONY: default all ci

default: exe
all: exe latex test
ci: all


# Executable

EXE = exe-$(NAME)/main.exe
SRCDIR = src
OUTDIR = _build/default/src
ROOTDIR = ..
INTERPRETERDIR = $(ROOTDIR)/interpreter
CLONEDIR = src/backend-interpreter/reference-interpreter
CLONERM = dune-project jslib
RUNNER = $(ROOTDIR)/src/backend-animation/interpreter-ocaml
OPAMPACKAGES = zarith menhir mdx tsort


.PHONY: exe

packages:
	opam install $(OPAMPACKAGES)

exe: $(CLONEDIR) packages
	rm -f ./$(NAME)
	dune build $(SRCDIR)/$(EXE)
	ln -f $(OUTDIR)/$(EXE) ./$(NAME)

$(CLONEDIR): $(shell find $(INTERPRETERDIR) -type f)
	rm -rf $(CLONEDIR)
	cp -R $(INTERPRETERDIR) $(CLONEDIR)
	rm -r $(CLONERM:%=$@/%)
	cp $@/../dune-ref-interp $@/dune


# IL Meta-interpreter

TEST ?= test-interpreter/sample.wast

ifeq ($(TEST),CORE)
TEST_PATHS := test-interpreter/spec-test-3/
else ifeq ($(TEST),FEATURES)
TEST_PATHS := test-interpreter/spec-test-3/bulk-memory \
              test-interpreter/spec-test-3/exceptions \
              test-interpreter/spec-test-3/gc \
              test-interpreter/spec-test-3/memory64 \
              test-interpreter/spec-test-3/multi-memory
else ifeq ($(TEST),OCAML_ALL)
TEST_PATHS := test-interpreter/spec-test-3/ \
              test-interpreter/spec-test-3/bulk-memory \
              test-interpreter/spec-test-3/exceptions \
              test-interpreter/spec-test-3/gc \
              test-interpreter/spec-test-3/memory64 \
              test-interpreter/spec-test-3/multi-memory
else ifeq ($(TEST),NON_SLOW)
TEST_PATHS := test-interpreter/spec-test-3/ \
              test-interpreter/spec-test-3/bulk-memory \
              test-interpreter/spec-test-3/exceptions \
              test-interpreter/spec-test-3/gc \
              test-interpreter/spec-test-3/memory64 \
              test-interpreter/spec-test-3/multi-memory \
              test-interpreter/spec-test-3/relaxed-simd \
              test-interpreter/spec-test-3/simd
else
TEST_PATHS := $(TEST)
endif


.PHONY = anim-test anim-test-all

anim-test: SPECTEC_EXTRA_FLAGS ?= -l
anim-test: SPECTEC_FLAGS ?= --animate --inline --new-interpreter-v
anim-test: exe
	./spectec $(SPECTEC_EXTRA_FLAGS) $(SPEC) $(SPECTEC_FLAGS) $(TEST_PATHS)

anim-test-all: exe
	$(MAKE) anim-test 'TEST=NON_SLOW'

# Wasm interpreter in OCaml

.PHONY = ocaml-build ocaml-clean ocaml-run ocaml-test ocaml-testall


SPEC ?= ../specification/wasm-3.0/* src/backend-animation/meta.spectec

ifeq ($(PRINT_DL),1)
  ifeq ($(UNDEP),1)
    SPECTEC_FLAGS = --animate --allow-partial-animation --inline --print-dl --typefamily-removal --remove-indexed-types --generate-ocaml "dl_codegen"
  else
    SPECTEC_FLAGS = --animate --allow-partial-animation --inline --print-dl --typefamily-removal --generate-ocaml "dl_codegen"
  endif
else
  ifeq ($(UNDEP),1)
    SPECTEC_FLAGS = --animate --allow-partial-animation --inline --typefamily-removal --remove-indexed-types --generate-ocaml "dl_codegen"
  else
    SPECTEC_FLAGS = --animate --allow-partial-animation --inline --typefamily-removal --generate-ocaml "dl_codegen"
  endif
endif


ocaml-build: exe
	mkdir -p src/backend-animation/interpreter-ocaml/build
	cp src/backend-animation/interpreter-ocaml/dl_runner.ml src/backend-animation/interpreter-ocaml/build/
	cp src/backend-animation/interpreter-ocaml/construct_ocaml.ml src/backend-animation/interpreter-ocaml/build/
	cp src/backend-animation/interpreter-ocaml/builtin.ml src/backend-animation/interpreter-ocaml/build/
	@echo "#### Generating OCaml interpreter."
	./spectec $(SPEC) $(SPECTEC_FLAGS)
	@echo "#### Compiling generated OCaml interpreter."
#	dune build --instrument-with landmarks src/backend-animation/interpreter-ocaml/build/dl_runner.exe
	dune build src/backend-animation/interpreter-ocaml/build/dl_runner.exe

ocaml-clean:
	rm -rf src/backend-animation/interpreter-ocaml/build

ocaml-run: ocaml-build
	dune exec ./src/backend-animation/interpreter-ocaml/build/dl_runner.exe $(SPEC) $(TEST_PATHS)

ocaml-test: ocaml-build
	@echo "#### Running OCaml interpreter test."
	$(MAKE) ocaml-run

ocaml-test-all: ocaml-build
	@echo "#### Running OCaml interpreter test."
	$(MAKE) ocaml-run 'TEST=OCAML_ALL'


# Latex

.PHONY: latex

latex: exe
	(cd test-latex && make all)


# Test

TESTDIRS = $(shell ls -d test-*)

.PHONY: test testpromote $(TESTDIRS) doc/example

test: exe $(TESTDIRS) doc/example

dunetest:
	@echo "#### Running (dune runtest)"
	@dune runtest && echo OK || (echo "####>" Failure running dune test. && echo "####>" Run \`make testpromote\` to accept changes in test expectations. && false)

testpromote:
	dune promote

$(TESTDIRS): test-%: exe
	@echo "#### Running (cd $@; make test)"
	@(cd $@ && ((make test >$(LOG) 2>&1 && (grep warning $(LOG) || true)) || (cat $(LOG) && echo "####>" Failure running $@. See log above. && false)))
	@echo "#### Running (cd $@; dune runtest)"
	@(cd $@ && dune runtest)

doc/example: exe
	@echo "#### Running (cd $@; make all)"
	@(cd $@ && make out clean >$(LOG) 2>&1 && rm -f $(LOG))


# Specification (copy to local workspace to make dune deps for tests happy)

SPECIFICATIONDIR = $(ROOTDIR)/specification
SPECCLONEDIR = _specification

$(SPECCLONEDIR): $(shell find $(SPECIFICATIONDIR) -type f)
	rm -rf $(SPECCLONEDIR)
	cp -R $(SPECIFICATIONDIR) $(SPECCLONEDIR)


# Spec document

.PHONY: spec spec-pdf

spec:
	(cd ../document/core && make main)

spec-pdf:
	(cd ../document/core && make pdf)

spec-html:
	(cd ../document/core && make html)

spec-clean:
	(cd ../document/core && make clean)


# Specification checks

check%:
	(cd ../specification && make $@)

sync%:
	(cd ../specification && make $@)


# Semantics checks

sem:
	(cd doc/semantics/il && make check)


# Cleanup

.PHONY: clean distclean

clean:
	dune clean
	rm -f src/frontend/parser.{automaton,conflicts}
	for dir in $(TESTDIRS); do (cd $$dir && make clean); done

distclean: clean spec-clean
	rm -f ./$(NAME)
	rm -rf $(CLONEDIR)
	for dir in $(TESTDIRS); do (cd $$dir && make distclean); done
	rm -rf src/backend-animation/interpreter-ocaml/build
