{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.ValidQC (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯

-- ** monomorphic version
data ValidQC (qc : QC) : Type where
  isValidQC :
    (∀ {ch : Chain} →
      ∙ ValidChain ch
      ∙ ch ∙blockId ≡ qc ∙blockId
        ─────────────────────────
        ch ∙round   ≡ qc ∙round   )
    ───────────────────────────────────────
    ValidQC qc

valid-qc₀ : ValidQC qc₀
valid-qc₀ = isValidQC λ where
  {[]}    _ refl → refl
  {_ ∷ _} _ id≡  → ⊥-elim $ noHashCollision˘ id≡

ValidProposal⇒qcValid :
  ValidProposal ms b
  ────────────────────
  ValidQC (b .blockQC)
ValidProposal⇒qcValid (_ ,  mk {ch = ch} ch∈ (connects∶ id≡ r≡ _))
    using vch ← chain-∈⇒ValidChain ch∈
    = isValidQC (λ vch′ id≡′ →
       subst ((_≡ _) ∘ _∙round )
             (uniqueChain vch vch′ (sym $ trans id≡′ id≡))
             (sym r≡))

b∈⇒qcValid : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ →
  let ls = s ＠ p
      mᵖ = Propose $ b signed-by roundLeader (b ∙round)
  in
    mᵖ ∈ ls .db
    ────────────────────
    ValidQC (b .blockQC)
b∈⇒qcValid {p}{b}{s} Rs ⦃ hp ⦄ m∈
  using srp ← sb∈⇒StepRegisterProposal Rs m∈
  with trE , srp▷ ← traceRs▷ Rs srp
  = ValidProposal⇒qcValid vp
  where
  open TraceExtension trE

  vp : ValidProposal ((intState ＠ p) .db) b
  vp = StepRegisterProposal⇒ValidProposal reachable′ srp▷
