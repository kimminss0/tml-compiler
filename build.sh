#!/bin/sh

eval $(opam env --switch=4.05.0 --set-switch)
rm -f typing.ml
git restore "typing.*"
make clean
make
echo "build: compiled with ocamlc $(ocamlc --version)"