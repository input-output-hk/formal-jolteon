{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.State.TC (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State.Messages ⋯
open import Jolteon.Properties.State.Invariants ⋯

qc-tc-last : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  Any (λ tc → qc ∈₁ qcs⁺ tc) (ls .tc-last)
  ────────────────────────────────────────
  qc ∙∈ s .history
qc-tc-last {p} (_ , refl , (_ ∎)) qc∈
  rewrite pLookup-replicate p initLocalState
  = contradict qc∈
qc-tc-last (_ , s-init , (s' ⟨ WaitUntil _ _ _ ∣ s ⟩←— tr)) qc∈
  = qc-tc-last (_ , s-init , tr) qc∈
qc-tc-last (_ , s-init , (s' ⟨ Deliver {tpm} _ ∣ s ⟩←— tr)) qc∈
  = qc-tc-last (_ , s-init , tr)
  $ subst (Any _) (receiveMsg-tcLast (honestTPMessage tpm)) qc∈
qc-tc-last (_ , s-init , (s' ⟨ DishonestLocalStep _ _ ∣ s ⟩←— tr)) qc∈
  = qc∈-monotonic (qc-tc-last (_ , s-init , tr) qc∈)
qc-tc-last {p}{qc} ⦃ hp ⦄
  (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {menv = menv} {ls′ = ls′} st ∣ s ⟩←— tr)) qc∈
  with Rs ← _ , s-init , tr
  with IH ← qc-tc-last {p}{qc} Rs
  with p ≟ p′
... | no p≢    rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = qc∈-++⁺ʳ $ IH qc∈
... | yes refl rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st
... | InitTC _ _ = qc∈-monotonic $ IH qc∈
... | InitNoTC _ _ = IH qc∈
... | ProposeBlock _ _ = qc∈-monotonic $ IH qc∈
... | ProposeBlockNoOp _ _ = IH qc∈
... | RegisterProposal _ _ _ _ _ = IH qc∈
... | EnoughTimeouts _ _ _ _ = qc∈-monotonic $ IH qc∈
... | RegisterTimeout _ _ _ _ = IH qc∈
... | RegisterTC _ _ _ _ = IH qc∈
... | TimerExpired _ _ = qc∈-monotonic $ IH qc∈
... | RegisterVote _ _ _ _ _ _ = IH qc∈
... | AdvanceRoundQC _ _ _ = ⊥-elim $ contradict qc∈
... | AdvanceRoundNoOp _ _ _ = IH qc∈
... | Lock _ _ = IH qc∈
... | CommitNoOp _ _ = IH qc∈
... | VoteBlock _ _ _ = qc∈-monotonic $ IH qc∈
... | VoteBlockNoOp _ _ = IH qc∈
... | Commit _ _ = IH qc∈
... | AdvanceRoundTC _ tc∈ _
  = L.All.lookup (tc∈⇒qc∈ (tc-db⊆history ⦃ hp ⦄ Rs tc∈)) (M.Any.drop-just qc∈)

tc-last⇒qc∈ : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .tc-last ≡ just tc
  ─────────────────────────────
  All (_∙∈ s .history) (qcs tc)
tc-last⇒qc∈ {p}{tc}{s = s} Rs tc≡ = L.All.tabulate λ qc∈ → qc-tc-last Rs (mqc qc∈)
  where
  mqc : qc ∈ qcs tc → Any (λ tc → qc ∈₁ qcs⁺ tc) ((s ＠ p) .tc-last)
  mqc qc∈ rewrite tc≡ = just qc∈
