#!/bin/sh

eval $(opam env --switch=4.14.2 --set-switch)
mv hw7 hw7.bak
make clean
cp typing_stub.ml typing.ml
make
mv hw7.bak hw7
echo "LSP setup: compiled with ocamlc $(ocamlc --version)"