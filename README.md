# First-order logic embedding in Matching logic

This project aims to embed First-order logic into Matching logic. The formalisation is implemented in Coq. 

In order to use this library, you need to install the Matching logic repository. Detailed tutorial can be found [here](https://github.com/harp-project/AML-Formalization/blob/master/README.md#aml-formalization)

## Content

1. `FOL.v`: First-order logic formalisation in a totally nameless representation.
2. `FOL_in_ML.v`: The embedding of FOL in ML.
3. `Hilbert.v`: The Hilbert-style proof system of FOL.
4. `PA.v`: Formalised Peano axioms. Used to test functions in `FOL_in_ML.v`.
