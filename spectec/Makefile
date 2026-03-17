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

# Build interpreter and example ocaml programs 

.PHONY: build_ocamlprog

SPEC ?= ../specification/testing2

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


TEST ?= test-ocaml/sample.wast

ifeq ($(TEST),CORE)
TEST_PATHS := test-interpreter/spec-test-3/ \
			  test-interpreter/spec-test-3/slow-return
else ifeq ($(TEST),FEATURES)
TEST_PATHS := test-interpreter/spec-test-3/bulk-memory \
              test-interpreter/spec-test-3/exceptions \
              test-interpreter/spec-test-3/gc \
              test-interpreter/spec-test-3/memory64 \
              test-interpreter/spec-test-3/multi-memory
else ifeq ($(TEST),ALL)
TEST_PATHS := test-interpreter/spec-test-3/ \
			  test-interpreter/spec-test-3/slow-return
              test-interpreter/spec-test-3/bulk-memory \
              test-interpreter/spec-test-3/exceptions \
              test-interpreter/spec-test-3/gc \
              test-interpreter/spec-test-3/memory64 \
              test-interpreter/spec-test-3/multi-memory
else
TEST_PATHS := $(TEST)
endif

build_ocamlprog: exe
	mkdir -p src/backend-animation/interpreter-ocaml/build
	cp src/backend-animation/interpreter-ocaml/dl_runner.ml src/backend-animation/interpreter-ocaml/build/
	cp src/backend-animation/interpreter-ocaml/construct_ocaml.ml src/backend-animation/interpreter-ocaml/build/
	cp src/backend-animation/interpreter-ocaml/builtin.ml src/backend-animation/interpreter-ocaml/build/
	./spectec $(SPEC) $(SPECTEC_FLAGS)
	@echo "#### spectec finished, compiling generated code"
#	dune build --instrument-with landmarks src/backend-animation/interpreter-ocaml/build/dl_runner.exe
	dune build src/backend-animation/interpreter-ocaml/build/dl_runner.exe
	@echo "#### dl-interpreter code compiled successfully, running tests ... "
	dune exec ./src/backend-animation/interpreter-ocaml/build/dl_runner.exe $(SPEC) $(TEST_PATHS)
# OCAML_LANDMARKS="on,output=stderr" dune exec ./src/backend-animation/interpreter-ocaml/build/dl_runner.exe $(TEST) $(SPEC)

run_ocaml: 
	cp src/backend-animation/interpreter-ocaml/dl_runner.ml src/backend-animation/interpreter-ocaml/build/
	cp src/backend-animation/interpreter-ocaml/construct_ocaml.ml src/backend-animation/interpreter-ocaml/build/
	cp src/backend-animation/interpreter-ocaml/builtin.ml src/backend-animation/interpreter-ocaml/build/
	@echo "#### compiling generated code"
	dune build src/backend-animation/interpreter-ocaml/build/dl_runner.exe
	@echo "#### dl-interpreter code compiled successfully, running tests ... "
	dune exec ./src/backend-animation/interpreter-ocaml/build/dl_runner.exe $(SPEC) $(TEST_PATHS)

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
