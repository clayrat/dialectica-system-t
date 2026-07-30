# Regenerate the extracted OCaml from Rocq, then build and run the demo.
#   make         - extract, build, and run
#   make extract - (re)generate dialectica.ml / dialectica.mli from Extract.v
#   make clean   - remove generated OCaml, the dune _build, and Rocq artifacts
#
# Uses the rocq-9.1 opam switch explicitly (the coq first on PATH may be older).

ROCQ ?= $(HOME)/.opam/rocq-9.1/bin/rocq

.PHONY: all extract run clean

all: run

dialectica.ml dialectica.mli: Extract.v ../theories/Realizer.vo
	$(ROCQ) compile -Q ../nbe-system-t/theories NbE -Q ../theories SystemT Extract.v

extract: dialectica.ml

run: dialectica.ml
	dune exec ./main.exe

clean:
	rm -f dialectica.ml dialectica.mli *.vo *.vok *.vos *.glob .*.aux
	rm -rf _build
