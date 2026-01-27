## An Agda mechanization of the Jolteon consensus protocol
[![CI](https://github.com/input-output-hk/formal-jolteon/workflows/Agda%20CI/badge.svg)](https://github.com/input-output-hk/formal-jolteon/actions)

Based on:

> **Jolteon and Ditto: Network-adaptive efficient consensus with asynchronous fallback**
>
> Rati Gelashvili, Lefteris Kokoris-Kogias, Alberto Sonnino, Alexander Spiegelman, Zhuolun Xiang
>
> *International Conference on Financial Cryptography and Data Security, 2022*

The methodology is briefly described in a [TYPES'25 abstract](https://omelkonian.github.io/data/publications/formal-jolteon-short.pdf):

> **Mechanized safety of Jolteon consensus in Agda**
>
> Orestis Melkonian, Mauro Jaskelioff, and James Chapman
>
> *31st International Conference on Types for Proofs and Programs, 2025*

which itself was first developed for the simpler [Streamlet protocol](https://github.com/input-output-hk/formal-streamlet), and is described in more detail in an [FMBC'25 paper](https://omelkonian.github.io/data/publications/formal-streamlet.pdf):

> **A readable and computable formalization of the Streamlet consensus protocol**
>
> Mauro Jaskelioff, Orestis Melkonian, and James Chapman
>
> *31st International Conference on Types for Proofs and Programs, 2025*


## HTML

Browse the Agda formalization in HTML [here](https://input-output-hk.github.io/formal-jolteon).

## WORK-IN-PROGRESS

We are actively working on more results in a private repo that we'll publish soon. These include:
- Proof of **liveness**
- **Conformance testing** an implementation against the formal specification:
  1. prove decidability results
  2. implement a sound-by-construction trace verifier
  3. extract these decidability proofs to decision procedures
