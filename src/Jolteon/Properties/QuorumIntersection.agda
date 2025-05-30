{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.QuorumIntersection (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.Votes ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.Steps.RVote ⋯

quorumIntersection : ∀ {vs hs : List Pid} →
    ∙ Unique vs
    ∙ Unique hs
    ∙ IsMajority vs
    ∙ MoreThanF hs
    ∙ All Honest hs
      ─────────────────────────────────────────
      ∃ λ p → Honest p × (p ∈ vs) × (p ∈ hs)
quorumIntersection {vs} {hs} u u′ maj maj′ ah′ =
  let
    vs∩ = hs ∩ vs

    u∩ : Unique vs∩
    u∩ = Unique-∩ u′

    open Nat; open ≤-Reasoning renaming (_∎ to _◻)

    len+ : length hs + length vs > nodes
    len+ = *-cancelˡ-< 3 _ _ $
      begin-strict
        3 * nodes
      ≡⟨⟩
        nodes + 2 * nodes
      ≤⟨ +-monoʳ-≤ nodes maj ⟩
        nodes + 3 * length vs
      <⟨ +-monoˡ-< _ maj′  ⟩
        3 * length hs + 3 * length vs
      ≡˘⟨ *-distribˡ-+ 3 (length hs) _ ⟩
        3 * (length hs + length vs)
      ◻

    len∩ : length vs∩ > 0
    len∩ =
      begin-strict
        0
      ≡˘⟨ n∸n≡0 nodes ⟩
        nodes ∸ nodes
      <⟨ ∸-monoˡ-< len+ ≤-refl ⟩
        (length hs + length vs) ∸ nodes
      ≤⟨ length-∩ u′ u ⟩
        length vs∩
      ◻

    p , p∈vs∩ = nonEmpty∈ {xs = vs∩} len∩
    p∈′ , p∈ = ∈-∩⁻ p hs vs p∈vs∩

    hp : Honest p
    hp = L.All.lookup ah′ p∈′

  in p , hp , p∈ , p∈′

private
  step-b≡ : ∀ {st st′ : Step} →
    ∙ StepVotes p b st
    ∙ StepVotes p b′ st′
    ∙ st ≡ st′
      ────────────────────
      b ≡ b′
  step-b≡ {st = _ ⊢ VoteBlock _ _ _} {st′ = _ ⊢ VoteBlock _ _ _}
    (_ , refl) (_ , refl) refl
    = refl

votedOnlyOnce' : ∀ {s} ⦃ _ : Honest p ⦄ → (Rs : Reachable s) →
  ∙ Rs ∋⋯ StepVotes p b
  ∙ Rs ∋⋯ StepVotes p b′
  ∙ b ∙round ≡ b′ ∙round
    ────────────────────
    b ≡ b′
votedOnlyOnce' {p}{b}{b′} ⦃ hp ⦄ Rs st∈ st∈′ br≡
  with b ≟ b′
... | yes b≡ = b≡
... | no  b≢
  with trE  , st-votes  ← traceRs⁺ Rs st∈
  with trE′ , st-votes′ ← traceRs⁺ Rs st∈′
  with factorRs⁺ Rs trE trE′
... | inj₁ st≡ = step-b≡ st-votes st-votes′ st≡
... | inj₂ (inj₁ b↝b′)
  = ⊥-elim QED
  where
  open TraceExtension⁺ trE
    using ()
    renaming (x to ≪s; y to ≫s; Ry to R≫s; step to st; y←x to s→)
  open TraceExtension⁺ trE′
    using ()
    renaming (x to ≪s′; y to ≫s′; step to st′)

  ≪ls  = ≪s  ＠ p
  ≪ls′ = ≪s′ ＠ p

  ≫ls  = ≫s  ＠ p

  sv : ShouldVote (≪s ＠ p) b
  sv = StepVotes⇒ShouldVote′ {s = ≪s} (st , refl , refl , st-votes)

  r≡ : b ∙round ≡ ≪ls .r-cur
  r≡ = sv .proj₁
  r> : b ∙round > ≪ls .r-vote
  r> = sv .proj₂ .proj₁

  rv≡b : b ∙round ≡ ≫ls .r-vote
  rv≡b = StepVotes⇒r≡ (st , ≪s , refl , refl , s→ ._ᴸ←—_.s≡ , st-votes)

  sv′ : ShouldVote (≪s′ ＠ p) b′
  sv′ = StepVotes⇒ShouldVote′ {s = ≪s′} (st′ , refl , refl , st-votes′)

  r≡′ : b′ ∙round ≡ ≪ls′ .r-cur
  r≡′ = sv′ .proj₁

  r>′ : b′ ∙round > ≪ls′ .r-vote
  r>′ = sv′ .proj₂ .proj₁

  s′←s : ≪s′ ↞— ≫s
  s′←s = b↝b′

  r≤′ : b′ ∙round ≤ ≪ls′ .r-vote
  r≤′ =
    Nat.≤-Reasoning.begin
      b′ ∙round
    ≡⟨ sym br≡ ⟩
      b ∙round
    ≡⟨ rv≡b ⟩
      ≫ls .r-vote
    ≤⟨ r-vote-mono R≫s s′←s ⟩
      ≪ls′ .r-vote
    Nat.≤-Reasoning.∎ where open Nat.≤-Reasoning

  QED : ⊥
  QED = Nat.<⇒≱ r>′ r≤′
... | inj₂ (inj₂ b′↝b)
  = ⊥-elim QED
  where
  open TraceExtension⁺ trE
    using ()
    renaming (x to ≪s; y to ≫s; step to st)
  open TraceExtension⁺ trE′
    using ()
    renaming (x to ≪s′; y to ≫s′; Ry to R≫s′; step to st′; y←x to s→′)

  ≪ls  = ≪s  ＠ p
  ≪ls′ = ≪s′ ＠ p
  ≫ls  = ≫s  ＠ p
  ≫ls′ = ≫s′ ＠ p

  sv : ShouldVote (≪s ＠ p) b
  sv = StepVotes⇒ShouldVote′ {s = ≪s} (st , refl , refl , st-votes)

  r≡ : b ∙round ≡ ≪ls .r-cur
  r≡ = sv .proj₁
  r> : b ∙round > ≪ls .r-vote
  r> = sv .proj₂ .proj₁

  sv′ : ShouldVote (≪s′ ＠ p) b′
  sv′ = StepVotes⇒ShouldVote′ {s = ≪s′} (st′ , refl , refl , st-votes′)

  r≡′ : b′ ∙round ≡ ≪ls′ .r-cur
  r≡′ = sv′ .proj₁

  r>′ : b′ ∙round > ≪ls′ .r-vote
  r>′ = sv′ .proj₂ .proj₁

  rv≡b′ : b′ ∙round ≡ ≫ls′ .r-vote
  rv≡b′ = StepVotes⇒r≡ (st′ , ≪s′ , refl , refl , s→′ ._ᴸ←—_.s≡ , st-votes′)

  s←s′ : ≪s ↞— ≫s′
  s←s′ = b′↝b

  r≤ : b ∙round ≤ ≪ls .r-vote
  r≤ =
    Nat.≤-Reasoning.begin
      b ∙round
    ≡⟨ br≡ ⟩
      b′ ∙round
    ≡⟨ rv≡b′ ⟩
      ≫ls′ .r-vote
    ≤⟨ r-vote-mono R≫s′ s←s′ ⟩
      ≪ls .r-vote
    Nat.≤-Reasoning.∎ where open Nat.≤-Reasoning


  QED : ⊥
  QED = Nat.<⇒≱ r> r≤

votedOnlyOnce : ∀ {s} ⦃ _ : Honest p ⦄ → Reachable s → let ms = s .history in
  ∙ p ∈ votes b  ms
  ∙ p ∈ votes b′ ms
  ∙ b ∙round ≡ b′ ∙round
    ────────────────────
    b ≡ b′
votedOnlyOnce ⦃ hp ⦄ Rs p∈ p∈′ r≡ =
  votedOnlyOnce' Rs
    (honest∈votes⇒StepVotes Rs hp p∈)
    (honest∈votes⇒StepVotes Rs hp p∈′)
    r≡

-- Observation 1
uniqueCertification : ∀ {s} → Reachable s →
  ∙ GloballyCertifiedBlockIn s b
  ∙ MoreThanF-Honest b′ s
  ∙ b ∙round ≡ b′ ∙round
    ─────────────────────
    b ≡ b′
uniqueCertification {b}{b′}{s} Rs gcb@(qc , cb , qc∈) maj′ r≡ =
  -- due to quorum intersection
  let
    ms = s .history

    p , hp , p∈ , p∈′ = quorumIntersection (getUnique qc)
                                           (Unique-nub {xs = honestVotes' b′ ms})
                                           (getQuorum qc)
                                           maj′
                                           (Honest-honestVotes b′ ms)

    v∈ = qc⇒vote {qc = qc} ⦃ hp ⦄ Rs qc∈ p∈ cb
    p∈′ , _ = p∈⇒hp b′ ms p∈′

  in
    votedOnlyOnce ⦃ hp ⦄ Rs v∈ p∈′ r≡
