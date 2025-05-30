# Decidability of logical propositions

All the logical propositional appearing in the formulation
of the Jolteon protocol (c.f. `Jolteon`) are in fact **decidable**,
meaning that we can utilize *proof-by-computation* to automatically discharge
proofs on closed terms. (c.f. `Jolteon.Test`).

Many of these are **already** decidable, by virtue of the decidability of their
building blocks.

The rest of these files provide manual proofs that this is indeed the case
for all other propositions where this is not automatically derived.

```agda
{-# OPTIONS --safe #-}
open import Jolteon.Assumptions

module Jolteon (⋯ : Assumptions) where

open import Jolteon.Base public
open import Jolteon.Assumptions public

open import Jolteon.Block ⋯ public
open import Jolteon.Message ⋯ public
open import Jolteon.Local.State ⋯ public
open import Jolteon.Local.Step ⋯ public
open import Jolteon.Global.State ⋯ public
open import Jolteon.Global.NoForging ⋯ public
  using (NoSignatureForging)
open import Jolteon.Global.Step ⋯ public
open import Jolteon.Global.Trace ⋯ public
```
