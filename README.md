## An Agda mechanization of the Jolteon consensus protocol [![CI](https://github.com/input-output-hk/formal-jolteon/workflows/CI/badge.svg)](https://github.com/input-output-hk/formal-jolteon/actions)

Based on:

    Gelashvili et al., 2022, May. "Jolteon and Ditto: Network-adaptive efficient consensus with asynchronous fallback"

## HTML

Browse the Agda formalization in HTML [here](https://input-output-hk.github.io/formal-jolteon).

## WORK-IN-PROGRESS

We are actively working on more results in a private repo that we'll publish soon. These include:
- Proof of **liveness**
- **Conformance testing** an implementation against the formal specification:
  1. prove decidability results
  2. implement a sound-by-construction trace verifier
  3. extract these decidability proofs to decision procedures
- **Sliced semantic view** of a single replica's behaviour:
  1. prove that the sliced semantics is *sound & complete* w.r.t. the global semantics
  2. extract a *sound & complete* sliced trace verifier for conformance testing
