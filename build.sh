#!/bin/bash
# Compile interface files
ocamlc -c logic.mli
ocamlc -c peano.mli

# Compile implementation files
ocamlc -c logic.ml
ocamlc -c peano.ml


# Link all files into an executable
# ocamlc -o main logic.cmo

