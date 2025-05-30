{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Safety.Core (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Votes ⋯
open import Jolteon.Properties.Steps ⋯

-- Definition 1:
--   We say that a block B is globally direct-committed if f+1 honest replicas
--   each successfully perform the Vote step on block B′ proposal in round B.r+1,
--   such that B′.qc certifies B.
--   ...
--
GloballyDirectCommitted : GlobalState → Block → Type
GloballyDirectCommitted s B =
  ∃ λ B′
    → (B′ ∙round ≡ 1 + B ∙round)
    × (B ←— B′)
    × MoreThanF-Honest B′ s

GDB⇒GCB : ∀ {s} → Reachable s →
  GloballyDirectCommitted s b
  ────────────────────────────
  GloballyCertifiedBlockIn s b
GDB⇒GCB {s = s} Rs (b′ , _ , b←b′ , hon-b′) = -, b←b′ , qc∈
  where
  p∈ : Propose _ ∈ s .history
  p∈ =
    let p , p∈hv = MoreThanF⇒∃ hon-b′
        _ , hp = p∈⇒hp b′ (s .history) p∈hv
        instance _ = hp
    in
       db⊆history Rs
     $ StepVotes⇒db∋ Rs
     $ honestVote⇒StepVotes Rs p∈hv

  qc∈ : b′ .blockQC ∙∈ s .history
  qc∈ = receivedQC $ L.Any.map (λ where refl → qc∈-Propose refl) p∈

GDB⇒ValidBlock : ∀ {s} → Reachable s →
  GloballyDirectCommitted s b
  ────────────────────────────
  ValidBlock b
GDB⇒ValidBlock Rs = GCB⇒ValidBlock Rs ∘ GDB⇒GCB Rs
