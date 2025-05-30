{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Safety.Consistency (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.Steps ⋯

open import Jolteon.Properties.Safety.Core ⋯
open import Jolteon.Properties.Safety.Lemma1 ⋯
open import Jolteon.Properties.Safety.Lemma3 ⋯

-- Theorem 2
safety : ∀ {s} → Reachable s →
  -- For every two globally direct-committed blocks B, B′...
  ∙ GloballyDirectCommitted s b
  ∙ GloballyDirectCommitted s b′
    ────────────────────────────
  -- ...either B ←—∗ B′ or B′ ←—∗ B.
    (b ←—∗ b′) ⊎ (b′ ←—∗ b)
safety {b = b}{b′}{s} Rs dcb dcb′
  with ¿ b ∙round ≤ b′ ∙round ¿
  -- As a corollary of Lemma3...
... | yes r≤ = inj₁ $ safetyLemma Rs cb′ r≤ dcb
  -- ...and the fact that every globally direct-committed block is certified.
  where cb′ = GDB⇒GCB Rs dcb′
... | no  r≰ = inj₂ $ safetyLemma Rs cb (Nat.≰⇒≥ r≰) dcb′
  where cb  = GDB⇒GCB Rs  dcb

-- Theorem 4
consistency′ : ∀ {s} → (Rs : Reachable s) →
  -- For every two committed blocks B, B′...
  ∙ Rs ∋⋯ StepCommits b
  ∙ Rs ∋⋯ StepCommits b′
    ───────────────────────
  -- ...either B ←—∗ B′ or B′ ←—∗ B.
    (b ←—∗ b′) ⊎ (b′ ←—∗ b)
consistency′ {b = b}{b′}{s} Rs cb cb′ =
  safety Rs (Commit⇒GlobalDirectCommit Rs cb) (Commit⇒GlobalDirectCommit Rs cb′)

-- A more immediate formulation of Theorem 4.
consistency : ∀ {s} → (Rs : Reachable s) →
  -- For every two committed blocks B, B′...
  ∙ (∃ λ p → ∃ λ (hp : Honest p) → b  ∈ (s ＠ʰ hp) .finalChain)
  ∙ (∃ λ p → ∃ λ (hp : Honest p) → b′ ∈ (s ＠ʰ hp) .finalChain)
    ──────────────────────────────────
  -- ...either B ←—∗ B′ or B′ ←—∗ B.
    (b ←—∗ b′) ⊎ (b′ ←—∗ b)
consistency Rs cb cb′ =
  let b̂  , cb̂  , b←b̂   = getCommitPoint Rs (ch∈⇒StepCommits∈ Rs cb)
      b̂′ , cb̂′ , b′←b̂′ = getCommitPoint Rs (ch∈⇒StepCommits∈ Rs cb′)
  in
    case consistency′ Rs cb̂ cb̂′ of λ where
      (inj₁ b̂←b̂′) → ←∗-factor (←∗-trans b←b̂ b̂←b̂′) b′←b̂′
      (inj₂ b̂′←b̂) → ←∗-factor b←b̂ (←∗-trans b′←b̂′ b̂′←b̂)
