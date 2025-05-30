{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Safety.Lemma3 (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
  hiding (begin_; _∎)
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Votes ⋯
open import Jolteon.Properties.QuorumIntersection ⋯
open import Jolteon.Properties.Steps ⋯
open import Jolteon.Properties.NonConsecutiveBlocks ⋯

open import Jolteon.Properties.Safety.Core ⋯
open import Jolteon.Properties.Safety.Lemma1 ⋯
open import Jolteon.Properties.Safety.Lemma2 ⋯

open Nat hiding (_≟_); open ≤-Reasoning hiding (stop)

-- ** these could be inlined, but we factor them out for type-checking performance
private
  safetyLemma-r≤0 : ∀ {b b′} → ∀ {s} → Reachable s →
    ∙ Genesis (b′ .blockQC)
    ∙ GloballyCertifiedBlockIn s b′
    ∙ GloballyDirectCommitted s b
    ∙ b′ ∙round ≡ 1 + r
    ∙ r >′ b ∙round
      ─────────────────────────────
      b ∙round ≤ 0
  safetyLemma-r≤0 {b = b}{b′} Rs refl gcb′ dcb refl r<′ = 0≥r
    where
    br≢0 : b ∙round ≢ 0
    br≢0 = ValidBlock⇒round⁺ {b} $ GDB⇒ValidBlock Rs dcb

    b′r>1 : b′ ∙round > 1
    b′r>1 = s≤s $
      begin
        1
      ≤⟨ n≢0⇒n>0 br≢0 ⟩
        b ∙round
      ≤⟨ n≤1+n _ ⟩
        suc (b ∙round)
      ≤⟨ ≤′⇒≤ r<′ ⟩
        _
      ∎

    bqc≡0 : (b′ .blockQC) ∙round ≡ 0
    bqc≡0 = GCB-QCGenesis Rs gcb′ refl

    0≥r : 0 ≥ b ∙round
    0≥r
      with refl ← bqc≡0
      using _ , hp , p∈ ← GCB⇒votes Rs gcb′
      with ⟫ b′ ∙tc? | nonConsecutivePointer {b = b′} Rs ⦃ hp ⦄ refl b′r>1 p∈
    ... | ⟫ just tc | just (refl , tc∈)
      =
      begin
        b ∙round
    -- By Lemma 2, this TC contains a qc-high with round ≥ r.
    --
    -- by GDB⇒qcHighRound, b ∙round ≤ rᵗᶜ
      ≤⟨ GDB⇒qcHighRound {tc = tc} Rs dcb tc∈ (≤′⇒≤ r<′) ⟩
        rᵗᶜ
    -- Consider a successful call by an honest replica to vote for B′.
    -- The only way to satisfy the predicate to vote is to satisfy (2),
    -- which implies B″.r ≥ qc-high ≥ B.r, which is a contradiction to r″<r.
    --
    -- by connects-to+ShouldVote(2), r″ = b′ .blockQC ∙round b′ ≥ rᵗᶜ
      ≤⟨ tc≤ ⟩
        b′ .blockQC ∙round
      ≡⟨⟩
        0
      ∎
      where
      rᵗᶜ = highestQC tc ∙round

      ∃vote : ∃ λ ls → ShouldVote ls b′
      ∃vote = StepVotes⇒ShouldVote Rs
            $ honest∈votes⇒StepVotes Rs hp p∈

      r≢qc+1 : b′ ∙round ≢ 1
      r≢qc+1 = Eq.≢-sym $ <⇒≢ b′r>1

      tc≤ : rᵗᶜ ≤ b′ .blockQC ∙round
      tc≤ with just (_ , tc≤) ← noInj₁ r≢qc+1 (∃vote .proj₂ .proj₂ .proj₂)
          = tc≤

  safetyLemma-r≤ : ∀ {b b′ b″ : Block} → ∀ {s} → Reachable s →
    ∙ ¬Genesis (b′ .blockQC)
    ∙ GloballyCertifiedBlockIn s b′
    ∙ GloballyDirectCommitted s b
    ∙ b′ ∙round ≡ 1 + r
    ∙ r >′ b ∙round
    ∙ (b′ .blockQC) ∙blockId ≡ b″ ∙blockId
    ∙ (b′ .blockQC) ∙round   ≡ b″ ∙round
      ────────────────────────────────────
      b ∙round ≤ b″ ∙round
  safetyLemma-r≤ {b = b}{b′}{b″} Rs ¬qc₀ gcb′ dcb refl r<′ b″id≡ b″r≡
    with dec
  -- B ←— Bᵣ₊₁ ←— ⋯ B″ ←— ⋯ ←— B′
  -- ↑    ↑         ↑          ↑
  -- r    r+1       r″         r′
    -- There are two cases to consider:
  ... | yes p = p
    --   ∙ r″ ≥ r
    --
    -- In the first case, by the induction assumption for round r″,
    -- B ←—∗ B″ and we are done.
  ... | no r≰
    --   ∙ r″ < r
    --
    -- In the second case, r″ < r < r′ (the right inequality is by the induction step),
    -- i.e. the rounds for B″ and B′ are not consecutive.
    = ⊥-elim (r≰ r″≥r)
    where
    r″ = b″ ∙round

    r″<r′ : 1 + r″ < b′ ∙round
    r″<r′ =
      begin-strict
        1 + r″
      <⟨ Nat.+-monoʳ-< 1 $ Nat.≰⇒> r≰ ⟩
        1 + b ∙round
      ≤⟨ Nat.m<n⇒m<1+n $ Nat.≤′⇒≤ r<′ ⟩
        b′ ∙round
      ∎

    r″≥r : r″ ≥ b ∙round
    r″≥r
      using _ , hp , p∈v ← GCB⇒votes Rs gcb′
      -- Hence, B′ must contain a TC for round r′-1.
      with ⟫ b′ ∙tc? | nonConsecutiveBlocks {b = b″} {b′ = b′} Rs ⦃ hp ⦄ (b″id≡ , b″r≡) r″<r′ p∈v
    ... | ⟫ just tc | just (refl , tc∈)
      =
      begin
        b ∙round
    -- By Lemma 2, this TC contains a qc-high with round ≥ r.
    --
    -- by GDB⇒qcHighRound, b ∙round ≤ rᵗᶜ
      ≤⟨ GDB⇒qcHighRound {tc = tc} Rs dcb tc∈ (Nat.≤′⇒≤ r<′) ⟩
        rᵗᶜ
    -- Consider a successful call by an honest replica to vote for B′.
    -- The only way to satisfy the predicate to vote is to satisfy (2),
    -- which implies B″.r ≥ qc-high ≥ B.r, which is a contradiction to r″<r.
    --
    -- by connects-to+ShouldVote(2), r″ = b′ .blockQC ∙round b′ ≥ rᵗᶜ
      ≤⟨ tc≤ ⟩
        b′ .blockQC ∙round
      ≡⟨ b″r≡ ⟩
        b″ ∙round
      ≡⟨⟩
        r″
      ∎
      where
      rᵗᶜ = highestQC tc ∙round

      ∃vote : ∃ λ ls → ShouldVote ls b′
      ∃vote = StepVotes⇒ShouldVote Rs $ honest∈votes⇒StepVotes Rs hp p∈v

      r≢qc+1 : b′ ∙round ≢ 1 + b′ .blockQC ∙round
      r≢qc+1 rewrite b″r≡ = Eq.≢-sym $ Nat.<⇒≢ r″<r′

      tc≤ : rᵗᶜ ≤ b′ .blockQC ∙round
      tc≤ with just (_ , tc≤) ← noInj₁ r≢qc+1 (∃vote .proj₂ .proj₂ .proj₂)
          = tc≤

-- Lemma 3
safetyLemma : ∀ {s} → Reachable s →
  ∙ GloballyCertifiedBlockIn s b′
  ∙ b ∙round ≤ b′ ∙round
  ∙ GloballyDirectCommitted s b
    ─────────────────────────────
    b ←—∗ b′
safetyLemma = go _ _ _ _
  where
  go< : ∀ n → (∀ {m} → m < n → _) → _

  go : ∀ n s b b′ → ⦃ n ≡ b′ ∙round ⦄ → Reachable s →
    ∙ GloballyCertifiedBlockIn s b′
    ∙ b ∙round ≤ b′ ∙round
    ∙ GloballyDirectCommitted s b
      ─────────────────────────────
      b ←—∗ b′
  go = Nat.<-rec _ go<

  go< n rec s b b′ ⦃ refl ⦄ Rs gcb′ r≤ dcb

    using qcᵇ′ , cb′ , qcᵇ′∈ ← gcb′
    using gcb ← GDB⇒GCB Rs dcb
    -- with qcᵇ  , cb  , qcᵇ∈  ←
    using br≢0 ← b ∙round ≢ 0
               ∋ (ValidBlock⇒round⁺ {b} $ GDB⇒ValidBlock Rs dcb)

    with b ∙round ≟ b′ ∙round
    -- By Observation 1, B ←—∗ B′ for every B′.r = B.r.
  ... | yes r≡
    using hon-b′ ← GCB⇒MoreThanF {b = b′} Rs gcb′
    rewrite b ≡ b′
          ∋ uniqueCertification {b = b} Rs gcb hon-b′ r≡
    = stop
    -- We now prove the lemma by induction on the round numbers r′ > B.r.
  ... | no  r≢
    using r< ← ≤∧≢⇒< r≤ r≢
    with ≤⇒≤′ r<
  ... | ≤′-refl
    -- * Base case: Let r′ = B.r + 1.

    -- B is globally direct-committed, so By Definition 1, there are f+1 honest replicas
    -- that prepare votes in round r′ = B.r + 1 on some block Bᵣ₊₁ such that B←—QCᴮ←—Bᵣ₊₁.
    with bᵣ₊₁ , refl , b← , maj ← dcb

    -- By Observation 1, only Bᵣ₊₁ can be certified in round r′.
    rewrite b′ ≡ bᵣ₊₁
          ∋ uniqueCertification {s = s} Rs gcb′ maj refl

    = stop¹ b←

  ... | ≤′-step r<′ -- with r<′ ← Nat.≤′⇒≤ r<′
    with (b′ .blockQC) ∙blockId ≟ genesisId
  ... | yes gen-b′
    = ⊥-elim (br≢0 br≡0)
  {-
  There should be TCs for every round between b′ ∙round and 0.
  In particular the TC for round (b′ ∙round -1) has a qchigh with round ≥ b ∙round (by lemma 2).
  But an honest vote for b′ implies that voting condition (2) holds, which implies qc₀ ≥ qchigh (tc) ≥ b ∙round.
  Which implies that b ∙round ≡ 0, which is impossible.
  -}
    where
    0≥r : 0 ≥ b ∙round
    0≥r = safetyLemma-r≤0 Rs gen-b′ gcb′ dcb refl r<′

    br≡0 : b ∙round ≡ 0
    br≡0 = n<1⇒n≡0 $ s≤s 0≥r
  ... | no ¬qc₀
    -- * Step: Let r′ = B.r + 2 + ...

    -- B ←— Bᵣ₊₁ ←— ⋯ ←— B′
    -- ↑    ↑            ↑
    -- r    r+1          r′

    -- Let B′ be a block certified in round r′ and let QCᴮ′ be its certificate.

    -- B is globally direct-committed, so by Definition 1, there are f+1 honest replicas
    -- that have locked high qc in round B.r+1.
    with bᵣ₊₁ , refl , b← , hon-bᵣ₊₁ ← dcb
    -- One of these replicas, ν, must also have prepared a vote that is included in QCᵇ′.
    -- (as QC formation requires 2f+1 votes and there are 3f+1 total replicas)
    -- using maj′ ← MoreThanF-Honest bᵣ₊₁ s ∋ hon-bᵣ₊₁
    -- using v , _ , _ , _ ← quorumIntersection
    --   (getUnique qcᵇ′)
    --   (Unique-nub {xs = honestVotes' bᵣ₊₁ (s .history)})
    --   (getQuorum qcᵇ′) maj′
    --   (Honest-honestVotes bᵣ₊₁ (s .history))

    = QED
    where
    qcᵇ″ = b′ .blockQC

    QED : b ←—∗ b′
    QED
      -- Let B″ ←— QCᴮ″ ←— B′ and denote r″ = B″.r = QCᴮ″.r

      using qcᵇ″∈ ← (qcᵇ″ ∙∈ s .history)
                  ∋ GCB⇒qc∈ Rs gcb′

      using b″ , _ , b″id≡ , b″r≡ ← qc∈⇒b∈ Rs ¬qc₀ qcᵇ″∈

      = continue b←∗b″ b″←b′
      where
      r″ = b″ ∙round

      r≤r″ : b ∙round ≤ b″ ∙round
      r≤r″ = safetyLemma-r≤ Rs ¬qc₀ gcb′ dcb refl r<′ b″id≡ b″r≡

      b←∗b″ : b ←—∗ b″
      b←∗b″ = rec r″<r′ s b b″ Rs cb″ r≤r″ dcb
        where
        cb″ : GloballyCertifiedBlockIn s b″
        cb″ = qcᵇ″ , (b″id≡ , b″r≡) , qcᵇ″∈

        r″<r′ : b″ ∙round < b′ ∙round
        r″<r′ = begin-strict
          (b″ ∙round)        ≡˘⟨ b″r≡ ⟩
          b′ .blockQC ∙round <⟨ GCB⇒ValidBlock Rs gcb′ ⟩
          (b′ ∙round)        ∎

      b″←b′ : b″ ←— qcᵇ″ ←— b′
      b″←b′ = (b″id≡ , b″r≡) , refl
