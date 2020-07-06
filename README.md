# Finite-dimensional type theory

This repository contains a highly experimental implementation of
finite-dimensional type theory, presented at HoTT/UF 2020:
https://hott-uf.github.io/2020/HoTTUF_2020_paper_11.pdf

The implementation makes use the construction of a type theory in type theory
presented by [Altenkirch and Kaposi](https://doi.org/10.1145/2914770.2837638).

The core rules can be found in 'FTT/Core.agda'. 

Definitional equalities are, where possible, proved by the rewrite pragma of
Agda. Where this is not possible, we often resort to postulates. These
postulates are mostly evident, but laborious to prove.

Some admissible rules in FTT, such as uniqueness of identity proofs, and a
formalization of semi-simplicial types (which is still in progress) can be found
in 'Examples'.
