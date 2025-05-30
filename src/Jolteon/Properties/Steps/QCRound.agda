{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.QCRound (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.Steps.Phases ⋯

-- ** Relating the round `qc-high` to `r-cur`.

AdvanceRoundLoop⇒AdvanceRoundQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ∙ ls .phase ≡ AdvancingRound
  ∙ ls .tc-last ≡ nothing
  ∙ ls .roundAdvanced? ≡ true
  ∙ qc -highest-qc-∈- ls .db
    ─────────────────────────
    1 + qc ∙round ≥ ls .r-cur
AdvanceRoundLoop⇒AdvanceRoundQC  {p} (_ , refl , (_ ∎)) ph≡ _ _ _
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
AdvanceRoundLoop⇒AdvanceRoundQC {p} {qc = qc} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡ tc≡ r≡ hqc∈
  with Rs ← _ , s-init , tr
  with IH ← AdvanceRoundLoop⇒AdvanceRoundQC {p} {qc = qc} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡ tc≡ r≡ hqc∈
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p} {s .stateMap} (honestTPMessage tpm)
  = IH ph≡ tc≡ r≡ hqc∈
... | DishonestLocalStep _ _
  = IH ph≡ tc≡ r≡ hqc∈
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡ tc≡ r≡ hqc∈
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | AdvancingRound⇒StepAdvances* ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | RegisterProposal m∈ x₁ x₂ x₃ x₄ | tt = contradict $ trans (sym r≡) ¬ra
  where
    ¬ra : ls′ .roundAdvanced? ≡ false
    ¬ra = AdvancingRound⇒¬roundAdvanced Rs ((_ ⊢ RegisterProposal m∈ x₁ x₂ x₃ x₄) ⦃ hp ⦄ , refl , refl , tt)
... | RegisterVote m∈ x₁ x₂ x₃ x₄ x₅ | tt = contradict $ trans (sym r≡) ¬ra
  where
    ¬ra : ls′ .roundAdvanced? ≡ false
    ¬ra = AdvancingRound⇒¬roundAdvanced Rs ((_ ⊢ RegisterVote m∈ x₁ x₂ x₃ x₄ x₅) ⦃ hp ⦄ , refl , refl , tt)
... | RegisterTimeout m∈ x₁ x₂ x₃ | tt = contradict $ trans (sym r≡) ¬ra
  where
    ¬ra : ls′ .roundAdvanced? ≡ false
    ¬ra = AdvancingRound⇒¬roundAdvanced Rs ((_ ⊢ RegisterTimeout m∈ x₁ x₂ x₃) ⦃ hp ⦄ , refl , refl , tt)
... | RegisterTC m∈ x₁ x₂ x₃ | tt = contradict $ trans (sym r≡) ¬ra
  where
    ¬ra : ls′ .roundAdvanced? ≡ false
    ¬ra = AdvancingRound⇒¬roundAdvanced Rs ((_ ⊢ RegisterTC m∈ x₁ x₂ x₃) ⦃ hp ⦄ , refl , refl , tt)
... | AdvanceRoundQC {qc = qc′} _ qc∈′ r≥ | tt
  = Nat.+-monoʳ-≤ 1 qc≥
  where
  qc≥ : qc ∙round ≥ qc′ ∙round
  qc≥ with ⟫ isHighest qc∈ qc≤ ← ⟫ hqc∈
      = qc≤ qc′ qc∈′

AdvanceRound⇒AdvanceRoundQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ∙ ls .phase ≡ Locking
  ∙ ls .tc-last ≡ nothing
  ∙ ls .roundAdvanced? ≡ true
  ∙ qc -highest-qc-∈- ls .db
    ─────────────────────────
    1 + qc ∙round ≥ ls .r-cur
AdvanceRound⇒AdvanceRoundQC {p} (_ , refl , (_ ∎)) ph≡ _ _ _
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
AdvanceRound⇒AdvanceRoundQC {p} {qc = qc} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡ tc≡ r≡ hqc∈
  with Rs ← _ , s-init , tr
  with IH ← AdvanceRound⇒AdvanceRoundQC {p} {qc = qc} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡ tc≡ r≡ hqc∈
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p} {s .stateMap} (honestTPMessage tpm)
  = IH ph≡ tc≡ r≡ hqc∈
... | DishonestLocalStep _ _
  = IH ph≡ tc≡ r≡ hqc∈
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡ tc≡ r≡ hqc∈
... | yes refl rewrite pLookup∘updateAt p  ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Locking⇒StepAdvances ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | AdvanceRoundNoOp ph≡′ _ _ | tt
  = AdvanceRoundLoop⇒AdvanceRoundQC ⦃ hp ⦄ Rs ph≡′ tc≡ r≡ hqc∈

Lock⇒AdvanceRoundQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ∙ ls .phase ≡ Committing
  ∙ ls .tc-last ≡ nothing
  ∙ ls .roundAdvanced? ≡ true
    ──────────────────────────────────
    1 + ls .qc-high ∙round ≥ ls .r-cur
Lock⇒AdvanceRoundQC {p} (_ , refl , (_ ∎)) ph≡ _ _
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Lock⇒AdvanceRoundQC {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡ tc≡ r≡
  with Rs ← _ , s-init , tr
  with IH ← Lock⇒AdvanceRoundQC {p} ⦃ hp ⦄ Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡ tc≡ r≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (1 + (s′ ＠ p) .qc-high ∙round ≥_) (sym $ receiveMsg-rCur tpm)
  $ subst (λ ◆ → 1 + ◆ ∙round ≥ _) (sym $ receiveMsg-qcHigh tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
       (subst (_≡ _) (receiveMsg-tcLast tpm) tc≡)
       (subst (_≡ _) (receiveMsg-roundA tpm) r≡)
... | DishonestLocalStep _ _
  = IH ph≡ tc≡ r≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡ tc≡ r≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Committing⇒StepLocks∗ ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | Lock ph≡ qc∈ | tt
  = AdvanceRound⇒AdvanceRoundQC {p} ⦃ hp ⦄ Rs ph≡ tc≡ r≡ qc∈

Commit⇒AdvanceRoundQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ∙ ls .phase ≡ Voting
  ∙ ls .tc-last ≡ nothing
  ∙ ls .roundAdvanced? ≡ true
    ──────────────────────────────────
    1 + ls .qc-high ∙round ≥ ls .r-cur
Commit⇒AdvanceRoundQC {p} (_ , refl , (_ ∎)) ph≡ _ _
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Commit⇒AdvanceRoundQC {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡ tc≡ r≡
  with Rs ← _ , s-init , tr
  with IH ← Commit⇒AdvanceRoundQC {p} Rs
  with IH≫ ← Lock⇒AdvanceRoundQC {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡ tc≡ r≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (1 + (s′ ＠ p) .qc-high ∙round ≥_) (sym $ receiveMsg-rCur tpm)
  $ subst (λ ◆ → 1 + ◆ ∙round ≥ _) (sym $ receiveMsg-qcHigh tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
       (subst (_≡ _) (receiveMsg-tcLast tpm) tc≡)
       (subst (_≡ _) (receiveMsg-roundA tpm) r≡)
... | DishonestLocalStep _ _
  = IH ph≡ tc≡ r≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡ tc≡ r≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Voting⇒StepCommits∗ ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | Commit     ph≡ _ | tt = IH≫ ph≡ tc≡ r≡
... | CommitNoOp ph≡ _ | tt = IH≫ ph≡ tc≡ r≡

Vote⇒AdvanceRoundQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ∙ ls .phase ≡ EnteringRound
  ∙ ls .tc-last ≡ nothing
  ∙ ls .roundAdvanced? ≡ true
    ──────────────────────────────────
    1 + ls .qc-high ∙round ≥ ls .r-cur
Vote⇒AdvanceRoundQC {p} (_ , refl , (_ ∎)) ph≡ _ _
  rewrite pLookup-replicate p initLocalState
  = Nat.≤-refl
Vote⇒AdvanceRoundQC {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡ tc≡ r≡
  with Rs ← _ , s-init , tr
  with IH ← Vote⇒AdvanceRoundQC {p} Rs
  with IH≫ ← Commit⇒AdvanceRoundQC {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡ tc≡ r≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (1 + (s′ ＠ p) .qc-high ∙round ≥_) (sym $ receiveMsg-rCur tpm)
  $ subst (λ ◆ → 1 + ◆ ∙round ≥ _) (sym $ receiveMsg-qcHigh tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
       (subst (_≡ _) (receiveMsg-tcLast tpm) tc≡)
       (subst (_≡ _) (receiveMsg-roundA tpm) r≡)
... | DishonestLocalStep _ _
  = IH ph≡ tc≡ r≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡ tc≡ r≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | EnteringRound⇒StepVotes∗ ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | VoteBlock ph≡ _ _   | tt , _ = IH≫ ph≡ tc≡ r≡
... | VoteBlockNoOp ph≡ _ | tt , _ = IH≫ ph≡ tc≡ r≡

InitNoTC⇒AdvanceRoundQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ∙ ls .phase ≡ Proposing
  ∙ ls .tc-last ≡ nothing
    ──────────────────────────────────
    1 + ls .qc-high ∙round ≥ ls .r-cur
InitNoTC⇒AdvanceRoundQC {p} (_ , refl , (_ ∎)) ph≡ _
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
InitNoTC⇒AdvanceRoundQC {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡ tc≡
  with Rs ← _ , s-init , tr
  with IH ← InitNoTC⇒AdvanceRoundQC {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡ tc≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (1 + (s′ ＠ p) .qc-high ∙round ≥_) (sym $ receiveMsg-rCur tpm)
  $ subst (λ ◆ → 1 + ◆ ∙round ≥ _) (sym $ receiveMsg-qcHigh tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
       (subst (_≡ _) (receiveMsg-tcLast tpm) tc≡)
... | DishonestLocalStep _ _
  = IH ph≡ tc≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡ tc≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Proposing⇒StepInits ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | InitTC {tc = tc} _ tc≡′ | tt = contradict $ trans (sym tc≡) tc≡′
... | InitNoTC ph≡ _          | tt = Vote⇒AdvanceRoundQC {p} ⦃ hp ⦄ Rs ph≡ tc≡
                                   $ EnteringRound⇒roundAdvanced ⦃ hp ⦄ Rs ph≡
