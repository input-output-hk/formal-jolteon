{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.RCur (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯


open Nat using (≤-refl; ≤-trans; m≤n⇒m≤1+n)

-- ** `r-cur` incresases monotonically.

r-cur-mono-—→ : ⦃ _ : Honest p ⦄ →
  s —→ s′
  ────────────────────────────────
  (s ＠ p) .r-cur ≤ (s′ ＠ p) .r-cur
r-cur-mono-—→ {p}{s} ⦃ hp ⦄ (LocalStep  {p = p′} {ls′ = ls′} st)
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap) = ≤-refl
... | yes refl rewrite pLookup∘updateAt p′ ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st
... | InitTC _ _ = ≤-refl
... | InitNoTC _ _ = ≤-refl
... | ProposeBlock _ _ = ≤-refl
... | ProposeBlockNoOp _ _ = ≤-refl
... | RegisterProposal _ _ _ _ _ = ≤-refl
... | RegisterVote _ _ _ _ _ _ = ≤-refl
... | RegisterTimeout _ _ _ _ = ≤-refl
... | RegisterTC _ _ _ _ = ≤-refl
... | EnoughTimeouts _ _ _ _ = ≤-refl
... | TimerExpired _ _ = ≤-refl
... | AdvanceRoundQC _ _ qc≥ = m≤n⇒m≤1+n qc≥
... | AdvanceRoundTC _ _ tc≥ = m≤n⇒m≤1+n tc≥
... | AdvanceRoundNoOp _ _ _ = ≤-refl
... | Lock _ _ = ≤-refl
... | Commit _ _ = ≤-refl
... | CommitNoOp _ _ = ≤-refl
... | VoteBlock _ _ _  = ≤-refl
... | VoteBlockNoOp _ _ = ≤-refl
r-cur-mono-—→ {p}{s} (WaitUntil _ _ _) =
  ≤-refl
r-cur-mono-—→ {p}{s} (Deliver {tpm} _) =
  subst ((s ＠ p) .r-cur ≤_) (sym $ receiveMsg-rCur (honestTPMessage tpm)) ≤-refl
r-cur-mono-—→ (DishonestLocalStep _ _) = ≤-refl


r-cur-mono : ⦃ _ : Honest p ⦄ →
  s′ ↞— s
  ────────────────────────────────
  (s ＠ p) .r-cur ≤ (s′ ＠ p) .r-cur
r-cur-mono (_ ∎) = ≤-refl
r-cur-mono {p = p} (_ ⟨ st ∣ s′ ⟩←— tr)
  = ≤-trans (r-cur-mono {p = p} tr)
            (r-cur-mono-—→ st)
