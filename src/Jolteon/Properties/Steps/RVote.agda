{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.RVote (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯

open Nat using (≤-refl; ≤-trans; m≤n⇒m≤1+n)

-- ** `r-vote` incresases monotonically.

r-vote-mono-—→ : ∀ {s}{s′}{p} → ⦃ _ : Honest p ⦄ → Reachable s →
  s —→ s′
  ────────────────────────────────
  (s ＠ p) .r-vote ≤ (s′ ＠ p) .r-vote
r-vote-mono-—→ {s}{_}{p} ⦃ hp ⦄ Rs (LocalStep  {p = p′} {ls′ = ls′} st)
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
... | EnoughTimeouts _ _ _ _ = r-vote-Bound ⦃ hp ⦄ Rs
... | TimerExpired _ _ = r-vote-Bound ⦃ hp ⦄ Rs
... | AdvanceRoundQC _ _ qc≥ = ≤-refl
... | AdvanceRoundTC _ _ tc≥ = ≤-refl
... | AdvanceRoundNoOp _ _ _ = ≤-refl
... | Lock _ _ = ≤-refl
... | Commit _ _ = ≤-refl
... | CommitNoOp _ _ = ≤-refl
... | VoteBlock _ _ (refl , r< , _) = Nat.<⇒≤ r<
... | VoteBlockNoOp _ _ = ≤-refl
r-vote-mono-—→ {s}{_}{p} _ (WaitUntil _ _ _)
  = ≤-refl
r-vote-mono-—→ {s}{_}{p} _ (Deliver {tpm} _)
  rewrite receiveMsg-ls≡ {p}{s .stateMap} (honestTPMessage tpm)
  = ≤-refl
r-vote-mono-—→ {s}{_}{p} _ (DishonestLocalStep _ _)
  = ≤-refl

r-vote-mono :  ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s →
   s′ ↞— s
  ──────────────────────────────────
  (s ＠ p) .r-vote ≤ (s′ ＠ p) .r-vote
r-vote-mono Rs (_ ∎) = ≤-refl
r-vote-mono {p = p} Rs@(_ , s-init , ⟪tr) (_ ⟨ st ⟩←— tr) =
  ≤-trans (r-vote-mono {p = p} Rs tr)
          (r-vote-mono-—→ (_ , s-init , ↞—-trans tr ⟪tr) st)
