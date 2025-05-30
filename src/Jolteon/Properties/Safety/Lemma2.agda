{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Safety.Lemma2 (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
  hiding (begin_; _∎)
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Votes ⋯
open import Jolteon.Properties.QuorumIntersection ⋯
open import Jolteon.Properties.Steps ⋯

open import Jolteon.Properties.Safety.Core ⋯
open import Jolteon.Properties.Safety.Lemma1 ⋯

-- Lemma 2
GDB⇒qcHighRound : ∀ {s} → Reachable s →
  -- If a block B is globally direct-committed...
  ∙ GloballyDirectCommitted s b
  -- ...then any higher-round TC...
  ∙ tc ∙∈ s .history
  ∙ b ∙round < tc ∙round
    ──────────────────────────────
  -- ...contains qc-high of round at least B.r.
    b ∙round ≤ highestQC tc ∙round
{- Proof:
  The TC has a majority of timeout messages.

  Because b is GDC, MoreThanF-Honest voted for b' (s.t. b ←— b′),
  and therefore executed the lock step in B'.r = B.r+1,
  and set qc_high to the QC certifying b.

  By quorum intersection, one of timeout messages in tc was sent by
  one of the honest replicas (say p) that executed the lock step in B.r+1

  Hence p set qc_high to a QC of round (b ∙round) *and* voted for the TC.

  Since qc_high never decreases, highestQC tc ∙round is at least b ∙round.
-}
GDB⇒qcHighRound {b = b} {tc = tc} {s = s} Rs dcb tc∈ br<
  with bᵣ₊₁ , refl , b←bᵣ₊₁@(refl , refl) , hon-bᵣ₊₁ ← dcb
  with p , hp , p∈ , p∈'
    ← quorumIntersection (getUniqueTC tc)
                         (Unique-nub {xs = honestVotes' bᵣ₊₁ (s. history)})
                         (majority-map⁺ (tc .tes) node (getQuorumTC tc))
                         hon-bᵣ₊₁
                         (Honest-honestVotes  bᵣ₊₁ (s. history))
  with ⟨ sᵣ₊₁ , Rsᵣ₊₁ , s←sᵣ₊₁ , eqᵣ₊ ⟩ , stᵣ₊₁ , refl , refl , stVotes
    ← traceRs▷ Rs (honestVote⇒StepVotes Rs p∈')
  with te , te∈ , refl ← L.Mem.find (L.Any.map⁻ p∈)
  with ⟨ sₜₑ  , Rsₜₑ  , s←sₜₑ  , eqₜₑ ⟩ , stₜₑ , ⟪sₜₑ , refl , refl , refl , stTimeout
    ← traceRs◃ Rs (te∈tc⇒Timeout Rs ⦃ hp ⦄ tc∈ refl te∈)
  = QED
  where
  trEᵣ₊₁ trEₜₑ : TraceExtension Rs
  trEᵣ₊₁ = ⟨ sᵣ₊₁ , Rsᵣ₊₁ , s←sᵣ₊₁ , eqᵣ₊ ⟩
  trEₜₑ  = ⟨ sₜₑ  , Rsₜₑ  , s←sₜₑ  , eqₜₑ ⟩

  qcb : QC
  qcb = bᵣ₊₁ .blockQC

  qctc : QC
  qctc = te ∙qcTE

  qctc≤ : qctc ≤qc highestQC tc
  qctc≤ = highestQC-correct tc (qcTE-lemma {tc = tc} te∈)

  lsᵣ₊₁ : LocalState
  lsᵣ₊₁ = sᵣ₊₁ ＠ʰ hp

  sᵣ₊₁▷Voting : sᵣ₊₁ ▷ StepVotes p bᵣ₊₁
  sᵣ₊₁▷Voting = stᵣ₊₁ , refl , refl , stVotes

  -- * voting for bᵣ₊₁ ⇒ qc-high set to qcb
  qcb≡qc-high : qcb ∙round ≡ (lsᵣ₊₁ .qc-high) ∙round
  qcb≡qc-high = vote-qc-high {b = bᵣ₊₁} ⦃ hp ⦄ Rsᵣ₊₁ sᵣ₊₁▷Voting refl

  lsₜₑ : LocalState
  lsₜₑ = sₜₑ ＠ʰ hp

  Timeout◃sₜₑ : StepTimeout p te ◃ sₜₑ
  Timeout◃sₜₑ = stₜₑ , ⟪sₜₑ , refl , refl , refl , stTimeout

  qctc≡qc-high : qctc ≡ lsₜₑ .qc-high
  qctc≡qc-high = timeout-qc-high {s = sₜₑ} {te = te} ⦃ hp ⦄ Timeout◃sₜₑ

  shouldVote : ShouldVote lsᵣ₊₁ bᵣ₊₁
  shouldVote = StepVotes⇒ShouldVote′ {s = sᵣ₊₁} ⦃ hp ⦄ sᵣ₊₁▷Voting

  rcur>rvote : lsᵣ₊₁ .r-cur > lsᵣ₊₁ .r-vote
  rcur>rvote = let eq , r> , _ = shouldVote in
    subst (suc (lsᵣ₊₁ .r-vote) ≤_) eq r>

  rvote>rcur : sᵣ₊₁ ↞— sₜₑ → lsᵣ₊₁ .r-cur < lsᵣ₊₁ .r-vote
  rvote>rcur sᵣ₊₁←sₜₑ =
    Nat.≤-reflexive $ timedOut?⇒r-cur-vote ⦃ hp ⦄ Rsₜₑ Timeout◃sₜₑ sᵣ₊₁←sₜₑ ter≡r-cur
    where
    r-cur≤ : lsₜₑ .r-cur ≤ lsᵣ₊₁ .r-cur
    r-cur≤ = r-cur-mono ⦃ hp ⦄ sᵣ₊₁←sₜₑ

    ter≡tcr : te ∙round ≡ tc ∙round
    ter≡tcr = L.All.lookup (getAllRound tc) te∈

    tc≡ : tc ∙round ≡ lsₜₑ .r-cur
    tc≡ = let open ≡-Reasoning in
      begin
        tc ∙round
      ≡˘⟨ ter≡tcr ⟩
        te ∙round
      ≡⟨ timeout-r-cur {s = sₜₑ} ⦃ hp ⦄ Timeout◃sₜₑ ⟩
        lsₜₑ .r-cur
      ∎

    r-curᵣ₊₁≡r : bᵣ₊₁ ∙round ≡ lsᵣ₊₁ .r-cur
    r-curᵣ₊₁≡r = shouldVote .proj₁

    tc< : tc ∙round ≤ 1 + b ∙round
    tc< = let open Nat.≤-Reasoning in
      begin
        tc ∙round
      ≡⟨ tc≡ ⟩
        lsₜₑ .r-cur
      ≤⟨ r-cur≤ ⟩
        lsᵣ₊₁ .r-cur
      ≡˘⟨ r-curᵣ₊₁≡r ⟩
        1 + b ∙round
      ∎

    ter≡r-cur : te ∙round ≡ lsᵣ₊₁ .r-cur
    ter≡r-cur = let open ≡-Reasoning in
      begin
        te ∙round
      ≡⟨ ter≡tcr ⟩
        tc ∙round
      ≡⟨ Nat.≤-antisym tc< br< ⟩
        1 + b ∙round
      ≡⟨ r-curᵣ₊₁≡r ⟩
        lsᵣ₊₁ .r-cur
      ∎

  sₜₑ←sᵣ₊₁ : sₜₑ ↞— sᵣ₊₁
  sₜₑ←sᵣ₊₁ = case (factorRs Rs trEᵣ₊₁ trEₜₑ) of λ where
    (inj₁ sᵣ₊₁←sₜₑ) → ⊥-elim (Nat.<-asym rcur>rvote (rvote>rcur sᵣ₊₁←sₜₑ))
    (inj₂ sₜₑ←sᵣ₊₁) → sₜₑ←sᵣ₊₁

  qc-high≤ : lsᵣ₊₁ .qc-high ≤qc lsₜₑ .qc-high
  qc-high≤ = qc-high-mono ⦃ hp ⦄ Rsᵣ₊₁ sₜₑ←sᵣ₊₁

  open Nat.≤-Reasoning

  qcb≤ : qcb ≤qc qctc
  qcb≤ = let open Nat.≤-Reasoning in
    begin
      qcb ∙round
    ≡⟨ qcb≡qc-high ⟩
      lsᵣ₊₁ .qc-high ∙round
    ≤⟨ qc-high≤ ⟩
      lsₜₑ .qc-high ∙round
    ≡˘⟨ cong _∙round qctc≡qc-high ⟩
      qctc ∙round
    ∎

  QED : b ∙round ≤ highestQC tc ∙round
  QED = let open Nat.≤-Reasoning in
    begin
      b ∙round
    ≡⟨⟩
      qcb ∙round
    ≤⟨ qcb≤ ⟩
      qctc ∙round
    ≤⟨ qctc≤ ⟩
      highestQC tc ∙round
    ∎
