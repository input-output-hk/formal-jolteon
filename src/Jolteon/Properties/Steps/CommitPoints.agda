{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.CommitPoints (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯

-- ** Relating `StepCommits∈` to a state's `finalChain`.

private
  ¬StepCommits⇒finalChain≡ : ∀ ⦃ _ : Honest p ⦄ (st : p ⦂ t ⊢ ls — menv —→ ls′) →
    ∙ ¬ StepCommits∈ b (_ ⊢ st)
    ∙ b ∈ ls′ .finalChain
      ────────────────────────
      b ∈ ls .finalChain
  ¬StepCommits⇒finalChain≡ {b = b} st b∉ b∈
    with st
  ... | InitTC _ _ = b∈
  ... | InitNoTC _ _ = b∈
  ... | ProposeBlock _ _ = b∈
  ... | ProposeBlockNoOp _ _ = b∈
  ... | RegisterProposal _ _ _ _ _ = b∈
  ... | EnoughTimeouts _ _ _ _ = b∈
  ... | RegisterTimeout _ _ _ _ = b∈
  ... | RegisterTC _ _ _ _ = b∈
  ... | TimerExpired _ _ = b∈
  ... | RegisterVote _ _ _ _ _ _ = b∈
  ... | AdvanceRoundQC _ _ _ = b∈
  ... | AdvanceRoundTC _ _ _ = b∈
  ... | AdvanceRoundNoOp _ _ _ = b∈
  ... | Lock _ _ = b∈
  ... | CommitNoOp _ _ = b∈
  ... | VoteBlock _ _ _ = b∈
  ... | VoteBlockNoOp _ _ = b∈
  ... | Commit _ _ = ⊥-elim $ b∉ b∈

ch∈⇒StepCommits∈ : ∀ {s} (Rs : Reachable s) →
  (∃ λ p → ∃ λ (hp : Honest p) → b ∈ (s ＠ʰ hp) .finalChain)
  ────────────────────────────────────────────────────────────
  Rs ∋⋯ StepCommits∈ b
ch∈⇒StepCommits∈ (_ , refl , (_ ∎)) (p , hp , b∈)
  rewrite let instance _ = hp in
          pLookup-replicate p initLocalState
  = contradict b∈
ch∈⇒StepCommits∈ {b} (_ , s-init , (_ ⟨ WaitUntil _ _ _ ∣ s ⟩←— tr)) (p , hp , b∈)
  = ch∈⇒StepCommits∈ (_ , s-init , tr) (p , hp , b∈)
ch∈⇒StepCommits∈ {b} (_ , s-init , (_ ⟨ Deliver {tpm} _ ∣ s ⟩←— tr)) (p , hp , b∈′)
  = ch∈⇒StepCommits∈ (_ , s-init , tr) (p , hp , b∈)
  where
  b∈ : b ∈ (s ＠ʰ hp) .finalChain
  b∈ = subst (b ∈_) (receiveMsg-final ⦃ hp ⦄ (honestTPMessage tpm) ) b∈′
ch∈⇒StepCommits∈ {b} (_ , s-init , (_ ⟨ DishonestLocalStep {env = env} _ _ ∣ s ⟩←— tr)) (p , hp , b∈′)
  = ch∈⇒StepCommits∈ (_ , s-init , tr) (p , hp , b∈′)
ch∈⇒StepCommits∈ {b = b} (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {ls′ = ls′} st ∣ s ⟩←— tr)) (p , hp , b∈′)
  with IH ← ch∈⇒StepCommits∈ {b = b} (s₀ , s-init , tr)
  with p ≟ p′
... | no p≢
  = there $ IH (p , hp , b∈)
  where
  s≡ : s' ＠ʰ hp ≡ s ＠ʰ hp
  s≡ = let instance _ = hp in
       pLookup∘updateAt′ p p′ (p≢ ∘ ↑-injective) (s .stateMap)

  b∈ : b ∈ (s ＠ʰ hp) .finalChain
  b∈ = subst (λ ◆ → _ ∈ ◆ .finalChain) s≡ b∈′
... | yes refl
  with StepCommits∈? b (_ ⊢ st)
... | yes commit-st = here commit-st
... | no ¬commit-st = there $ IH (p , hp , b∈)
  where
  ls′≡ : s' ＠ p ≡ ls′
  ls′≡ = pLookup∘updateAt _ (s .stateMap)

  b∈ : b ∈ (s ＠ p) .finalChain
  b∈ = ¬StepCommits⇒finalChain≡ st ¬commit-st
     $ subst (λ ◆ → _ ∈ ◆ .finalChain) ls′≡ b∈′

getCommitPoint : ∀ {s} → (Rs : Reachable s) →
  Rs ∋⋯ StepCommits∈ b
  ─────────────────────────────
  ∃ λ b′ → Rs ∋⋯ StepCommits b′
         × b ←—∗ b′
getCommitPoint {b} (_ , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) b∈
  = getCommitPoint (_ , s-init , tr) b∈
getCommitPoint {b} (_ , s-init , (_ ⟨ Deliver _ ⟩←— tr)) b∈
  = getCommitPoint (_ , s-init , tr) b∈
getCommitPoint {b} (_ , s-init , (_ ⟨ DishonestLocalStep {env} _ _ ⟩←— tr)) b∈
  = getCommitPoint (_ , s-init , tr) b∈
getCommitPoint (s , s-init , (_ ⟨ LocalStep p ⟩←— tr))
  (there st∈)
  = let b′ , st∈ , b←b′ = getCommitPoint (s , s-init , tr) st∈
    in b′ , there st∈ , b←b′
getCommitPoint {b}
  (_ , _ , (_ ⟨ LocalStep (Commit {ch = b′ ∷ ch} _ (final∈ _ _ (_ ∷ ch∈ ⊣ _) _ , _)) ⟩←— tr))
  (here b∈ch)
  = b′ , here refl , b←b′
  where
  vch : ValidChain (b′ ∷ ch)
  vch = chain-∈⇒ValidChain ch∈

  b∈ : b ∈ b′ ∷ ch
  b∈ = b∈ch

  b←b′ : b ←—∗ b′
  b←b′ = b∈⇒b← vch b∈
