all: build

build:
	dune build

test:
	dune test

test-rerun:
	dune test --force

doc:
	dune build @doc

install: build doc
	mkdir -p _install
	cp -rf _build/default/_doc/_html/ _install/doc
	cp -f ./LICENSE _install/LICENSE
	cp -f ./README.md _install/README.md
	cp -f _build/default/bin/main.exe _install/main.exe

system-test: install
	./system-tests/run_tests.sh

docopen: doc
	open _build/default/_doc/_html/index.html

clear: clean

clean:
	rm -fr _build
	rm -fr _install

setup:
	opam update
	opam upgrade
	opam install dune ppx_deriving odoc

.PHONY: all build install test test-rerun system-test doc docopen setup clear clean