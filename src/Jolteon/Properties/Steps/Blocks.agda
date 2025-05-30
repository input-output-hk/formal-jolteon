{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.Blocks (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.State.Messages ⋯
open import Jolteon.Properties.State.Invariants ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.Steps.Voting ⋯
open import Jolteon.Properties.Steps.QCHigh ⋯


{-
StepProposes⇒ValidBlock : ∀ {s} → Reachable s →
  s ▷ StepProposes b
  ──────────────────
  ValidBlock b
StepProposes⇒ValidBlock {b}{s} Rs (st , t≡ , ls≡ , st-proposes)
  with st .theStep | st-proposes
... | ProposeBlock {txn = txn} ph≡ p≡L | refl
  = r<
  where
  -- _ls = st .stepArgs .proj₂ .proj₂ .proj₁
  _ls = s ＠ st .stepArgs .proj₁

  b≡ : b ≡ mkBlockForState _ls txn
  b≡
    with ⟫ st .theStep | ⟫ st-proposes
  ... | ⟫ ProposeBlock refl refl | ⟫ b≡
      = subst (λ ◆ → b ≡ mkBlockForState ◆ txn) (sym ls≡) st-proposes

  ≪db = _ls .db
  qch = _ls .qc-high

  qch∈ : qch ∙∈ ≪db
  qch∈ = qc-high∈db Rs

  qc≡ : b .blockQC ≡ _ls .qc-high
  qc≡ = subst (λ ◆ → ◆ .blockQC ≡ qch) (sym b≡) refl

  r< : b ∙round > b .blockQC ∙round
  r< =
    Nat.≤-Reasoning.begin-strict
      ((b .blockQC) ∙round)
    ≡⟨ cong _∙round qc≡  ⟩
      (_ls .qc-high) ∙round
    <⟨ Init⇒QCBound Rs $ subst (λ ◆ → ◆ .phase ≡ _) (sym ls≡) ph≡ ⟩
      (_ls .r-cur)
    ≡⟨ subst (λ ◆ → _ls .r-cur ≡ ◆ ∙round) (sym b≡) refl ⟩
      (b ∙round)
    Nat.≤-Reasoning.∎
    where open Nat.≤-Reasoning
-}


-- b∈⇒ch∈ NOT TRUE for s. history
-- counterexample: Adversary proposes Block b extendind genesis but round ≡ 0.
-- This is only true if its in a local database (i.e. it has been validated).
b∈⇒ch∈ : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s →  let db = (s ＠ p) .db  in
  b ∙∈ db
  ────────────────────────
  ∃ λ (ch : Chain) →
    (b ∷ ch) ∙∈ db
b∈⇒ch∈ {p} (_ , refl , (_ ∎)) b∈
  rewrite pLookup-replicate p initLocalState
  = contradict b∈
b∈⇒ch∈ {p}{b} ⦃ hp ⦄ (_ , s-init , (s' ⟨ st₀ ∣ s ⟩←— tr)) b∈
 with Rs ← _ , s-init , tr
 with IH ← b∈⇒ch∈ {p}{b} Rs
 with st₀
... | WaitUntil _ _ _
  = IH b∈
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p}{s .stateMap} (honestTPMessage tpm)
  = IH b∈
... | DishonestLocalStep _ _ = IH b∈
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢    rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH b∈
... | yes refl rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st
... | InitTC _ _
  = IH b∈
... | InitNoTC _ _
  = IH b∈
... | ProposeBlockNoOp _ _
  = IH b∈
... | EnoughTimeouts _ _ _ _
  = IH b∈
... | RegisterTimeout _ _ _ _
  =  map₂ chain-∈-mono $ IH b∈
... | RegisterTC _ _ _ _
  = map₂ chain-∈-mono $ IH b∈
... | TimerExpired _ _
  = IH b∈
... | RegisterVote _ _ _ _ _ _
  = map₂ chain-∈-mono $ IH b∈
... | AdvanceRoundQC _ _ _
  = IH b∈
... | AdvanceRoundTC _ _ _
  = IH b∈
... | AdvanceRoundNoOp _ _ _
  = IH b∈
... | Lock _ _
  = IH b∈
... | Commit _ _
  = IH b∈
... | CommitNoOp _ _
  = IH b∈
... | VoteBlock _ _ _
  = IH b∈
... | VoteBlockNoOp _ _
  = IH b∈
... | ProposeBlock {txn = txn} ph≡ _
  = IH b∈
... | RegisterProposal _ _ _ _ vp@(_ , mk {ch} ch∈ b↝)
  with ⟫ b∈
... | ⟫ there b∈ = map₂ chain-∈-mono $ IH b∈
... | ⟫ here refl
   with b .blockQC ≟ qc₀
... | yes refl
  = [] , here refl ∷ []
       ⊣ connects∶ refl refl
                   (ValidProposal⇒ValidBlock vp)
... | no qc₀≢  = ch , b∈ ∷  chain-∈-mono ch∈  ⊣ b↝
