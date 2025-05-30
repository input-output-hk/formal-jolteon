{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.Certification (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.Steps.Voting ⋯
open import Jolteon.Properties.Steps.Blocks ⋯
open import Jolteon.Properties.Votes ⋯
open import Jolteon.Properties.ValidQC ⋯


GCB⇒b∈ : ∀ {s} → Reachable s →
  GloballyCertifiedBlockIn s b
  ────────────────────────────
  b ∙∈ s .history
GCB⇒b∈ Rs (qc , bcert@(b≡ , _) , qc∈)
  with b′ , b′∈ , b′≡ , _ ← qc∈⇒b∈ Rs (¬certified-by-genesis {qc = qc} bcert) qc∈
  with refl ← ♯-inj {y = b′} (trans (sym b≡) b′≡)
  = b′∈

GCB⇒qc∈ : ∀ {s} → Reachable s →
  GloballyCertifiedBlockIn s b
  ────────────────────────────
  b .blockQC ∙∈ s .history
GCB⇒qc∈ Rs = b∈⇒qc∈ ∘ GCB⇒b∈ Rs

GCB⇒ValidBlock : ∀ {s} → Reachable s →
  GloballyCertifiedBlockIn s b
  ────────────────────────────
  ValidBlock b
GCB⇒ValidBlock {b}{s} Rs gcb@(qc , cb , qc∈)
  with p , p∈ , hp ← qc⇒hp qc
  = QED
  where
  _sb = b signed-by roundLeader (b ∙round)
  mᵖ = Propose _sb

  mᵖ∈ : mᵖ ∈ ((s ＠ʰ hp) .db)
  mᵖ∈ = StepVotes⇒db∋ {b = b} ⦃ hp ⦄ Rs (honest∈votes⇒StepVotes Rs hp (qc⇒vote ⦃ hp ⦄ Rs qc∈ p∈ cb))

  srp : Rs ∋⋯ StepRegisterProposal p _sb
  srp = sb∈⇒StepRegisterProposal {sb = _sb} ⦃ hp ⦄ Rs mᵖ∈

  QED : ValidBlock b
  QED
    with _ , _ ⊢ RegisterProposal _ _ _ _ vp , _ , refl , refl , refl ← traceRs▷ Rs srp
    = ValidProposal⇒ValidBlock vp

GCB⇒b∈h : ∀ {s} → Reachable s →
  let mᵖ = Propose $ b signed-by roundLeader (b ∙round) in
  GloballyCertifiedBlockIn s b
  ─────────────────────────────────────────────────
  ∃ λ p → ∃ λ (hp : Honest p) → mᵖ ∈ (s ＠ʰ hp) .db
GCB⇒b∈h {b}{s} Rs gcb
  with p , hp , p∈ ← GCB⇒votes Rs gcb
  = p , hp , b∈
  where
  b∈ : _ ∈ (s ＠ʰ hp) .db
  b∈ = StepVotes⇒db∋ ⦃ hp ⦄ Rs $ honest∈votes⇒StepVotes Rs hp p∈

GCB-QCGenesis : ∀ {s} → Reachable s →
  ∙ GloballyCertifiedBlockIn s b
  ∙ Genesis (b . blockQC)
    ────────────────────────────
    (b . blockQC) ∙round ≡ 0
GCB-QCGenesis Rs gcb id≡
  using p , hp , b∈ ← GCB⇒b∈h Rs gcb
  with isValidQC id≡⇒r≡ ← b∈⇒qcValid Rs ⦃ hp ⦄ b∈
  = sym (id≡⇒r≡ [] (sym id≡))
