# First-order logic embedding in matching logic

This project aims to embed first-order logic into matching logic. The formalisation is implemented in Coq. The project is based on a [formalisation of first-order logic](https://github.com/mark-koch/firstorder-proof-mode).

## Requirements
* [Matching logic repository installed](https://github.com/harp-project/AML-Formalization/blob/master/README.md#aml-formalization)
* The Coq Proof Assistant, version 8.12.1

## Build

Run the Makefile or compile the files in the following order:
1. `FOL.v`
2. `Tarski.v`
3. `VectorTech.v`
4. `Deduction.v`
5. `PA.v`
6. `Hilbert.v`
7. `FOL_in_ML.v`

## Content

1. `FOL.v`: First-order logic formalisation in a totally nameless representation.
2. `FOL_in_ML.v`: The embedding of FOL in ML.
3. `Hilbert.v`: The Hilbert-style proof system of FOL.
4. `PA.v`: Formalised Peano axioms. Used to test functions in `FOL_in_ML.v`.
