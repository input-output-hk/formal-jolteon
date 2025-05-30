# Jolteon Properties to Test
<!--
```agda
{-# OPTIONS --safe #-}
open import Jolteon.Assumptions

open import Prelude

module Jolteon.TestProperties (⋯ : _) where

open Assumptions ⋯
open import Jolteon ⋯
import Jolteon.Properties.State.Invariants ⋯ as P

private variable A : Type
```
-->

## Threshold Signatures
```agda
module _ (ts : ThresholdSig A) where
```

Vote shares of a threshold signature do not contain duplicates and form a majority
```agda
  ts-unique   : Unique (ts .shares)
  ts-majority : IsMajority (ts .shares)
```
<!--
```agda
  ts-unique = getUnique ts
  ts-majority = getQuorum ts
```
-->


## Quorum Certificates
```agda
module _ (qc : QC) where
```

A QC has a payload of BlockId `bid` and a round `r`.
The round `r` should be equal to the round of the block whose id is `bid`.
<!--
```agda
  instance
    _ = HasRound   (BlockId × Round) ∋ λ where ._∙round   → proj₂
    _ = HasBlockId (BlockId × Round) ∋ λ where ._∙blockId → proj₁
```
-->
```agda
  qc-round = ∀ (b : Block) →
    b ∙blockId ≡ qc .payload ∙blockId
    ─────────────────────────────────
    b ∙round   ≡ qc .payload ∙round
```


## Timeout Certificates
```agda
module _ (tc : TC) where
```

The shares in a timeout certificate are unique, form a majority, and have proper rounds:
```agda
  tc-unique   : UniqueBy node (tc .tes)
  tc-majority : IsMajority (tc .tes)
  tc-rounds   : ∀[ te ∈ tc .tes ]
                    (te ∙round       ≡ tc .roundTC)
                  × (te ∙qcTE ∙round < tc .roundTC)
```
<!--
```agda
  tc-unique = getUniqueTC tc
  tc-majority = getQuorumTC tc
  tc-rounds = L.All.tabulate
    λ p → L.All.lookup (getAllRound tc) p , L.All.lookup (getQCBound tc) p
```
-->


Other properties talk about the function that extracts a list of QCs from the TC,
and the function that obtains the maximum QC from the TC.
Should we test that? (these functions might not exist in an implementation).

## Blocks

```agda
block-round-advances : ∀ (b : Block) →
  ValidBlock b
  ──────────────────────────────
  b ∙round > (b .blockQC) ∙round
```
<!--
```agda
block-round-advances _ p = p
```
-->


## Chains

The blockId of chain is the blockId of its head.

```agda
blockchain-id : ∀ (b : Block) (ch : Chain) →
    b -connects-to- ch
    ─────────────────────────────────────
    (b .blockQC) ∙blockId ≡ ch ∙blockId
  × (b .blockQC) ∙round   ≡ ch ∙round
```
<!--
```agda
blockchain-id _ _ bch = bch .idMatch , bch .roundMatch
```
-->


## Local State

The following are properties related to the local state of a node.

```agda
module _ (s : GlobalState) (p : Pid) ⦃ _ : Honest p ⦄ (Rs : Reachable s) (let ls = s ＠ p) where
```

* The `qc-high` in the local state is always obtainable
  from the database of messages received.

```agda
  qc-high∈db : ls .qc-high ∙∈ ls .db
```
<!--
```agda
  qc-high∈db = P.qc-high∈db Rs
```
-->


* If `tc-last` is set to a TC `tc` then `r-cur` is set to one more
  than the `tc` round.

```agda
  tc-last-r≡ : ∀[ tc ∈ ls .tc-last ]  ls .r-cur ≡ 1 + tc ∙round
```
<!--
```agda
  tc-last-r≡ = P.tc-last-r≡ Rs
```
-->

* The field `r-vote` is always less or equal to `1 + r-cur`.

```agda
  r-vote-bound : ls .r-vote ≤ 1 + ls .r-cur
```
<!--
```agda
  r-vote-bound = P.r-vote-Bound Rs
```
-->

There are many more properties, but they require more complex testing as they are related to
 * Global state: for example, the whole history of messages in the system (`history` in the formalization)
 * The effect of a step on state: for example monotonicity of `r-cur`.
 * Specific steps: for example, properties that assert that certain conditions hold before voting (or after voting).
