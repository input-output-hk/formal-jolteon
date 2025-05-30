# Decidable propositions appearing in the Jolteon protocol
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Decidability (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Decidability.Core ⋯ public
open import Jolteon.Decidability.VoteSharesOf ⋯ public
open import Jolteon.Decidability.HighestQC ⋯ public
open import Jolteon.Decidability.AllTCs ⋯ public
open import Jolteon.Decidability.Final ⋯ public
open import Jolteon.Decidability.SmartConstructors ⋯ public
```
