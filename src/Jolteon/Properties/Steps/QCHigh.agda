{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.QCHigh (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.Steps.Phases ⋯
open import Jolteon.Properties.QuorumIntersection ⋯

open Nat using (≤-refl; ≤-trans)

qc-high-mono-—→ : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s →
  s —→ s′
  ──────────────────────────────────────
  (s ＠ p) .qc-high ≤qc (s′ ＠ p) .qc-high
qc-high-mono-—→ Rs (WaitUntil _ _ _) = ≤-refl
qc-high-mono-—→ {p = p}{s = s} Rs (Deliver {tpm} _) =
  subst ((s ＠ p) .qc-high ≤qc_) (sym $ receiveMsg-qcHigh (honestTPMessage tpm)) ≤-refl
qc-high-mono-—→ {p = p}{s = s} Rs (DishonestLocalStep _ _) = ≤-refl
qc-high-mono-—→ {p = p}{s = s} ⦃ hp ⦄ Rs (LocalStep {p = p′} {ls′ = ls′} st)
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = ≤-refl
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st
... | Lock _ (isHighest qc∈ allqc≤) = allqc≤ ((s ＠ʰ hp) .qc-high) (qc-high∈db ⦃ hp ⦄ Rs)
... | InitTC _ _ = ≤-refl
... | InitNoTC _ _ = ≤-refl
... | ProposeBlock _ _ = ≤-refl
... | ProposeBlockNoOp _ _ = ≤-refl
... | RegisterProposal _ _ _ _ _ = ≤-refl
... | RegisterVote _ _ _ _ _ _ = ≤-refl
... | RegisterTimeout _ _ _ _ = ≤-refl
... | RegisterTC _ _ _ _ = ≤-refl
... | EnoughTimeouts _ _ _ _ = ≤-refl
... | TimerExpired _ _ = ≤-refl
... | AdvanceRoundQC _ _ _ = ≤-refl
... | AdvanceRoundTC _ _ _ = ≤-refl
... | AdvanceRoundNoOp _ _ _ = ≤-refl
... | Commit _ _ = ≤-refl
... | CommitNoOp _ _ = ≤-refl
... | VoteBlock _ _ _ = ≤-refl
... | VoteBlockNoOp _ _ = ≤-refl

qc-high-mono : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s →
  s′ ↞— s
  ──────────────────────────────────────
  (s ＠ p) .qc-high ≤qc (s′ ＠ p) .qc-high
qc-high-mono Rs (_ ∎) = ≤-refl
qc-high-mono {p = p} Rs (_ ⟨ st ∣ s′ ⟩←— s→s′)
  = ≤-trans (qc-high-mono {p = p} Rs s→s′)
            (qc-high-mono-—→ (extendRs Rs s→s′) st)

AdvanceRound⇒QCBound : ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s)(let ls = s ＠ p) →
  ls .phase ≡ Locking
  ─────────────────────────────────────────────
  AllQC (λ qc → qc ∙round < ls .r-cur) (ls .db)
AdvanceRound⇒QCBound {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
AdvanceRound⇒QCBound {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡
 with Rs ← _ , s-init , tr
 with IH ← AdvanceRound⇒QCBound {p} Rs
 with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p}{s .stateMap} (honestTPMessage tpm) = IH ph≡
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Locking⇒StepAdvances ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | AdvanceRoundNoOp ph≡ aqc _ | tt
  = aqc

-- ls .qc-high ∙round < ls .r-cur

Lock⇒QCBound : ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s)(let ls = s ＠ p) →
  ls .phase ≡ Committing
  ──────────────────────────────
  ls .qc-high ∙round < ls .r-cur
Lock⇒QCBound {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Lock⇒QCBound {p}  ⦃ hp ⦄(_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡
 with Rs ← _ , s-init , tr
 with IH ← Lock⇒QCBound {p} Rs
 with IH≫ ← AdvanceRound⇒QCBound {p} Rs
 with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (λ ◆ → ◆ ∙round < (s′ ＠ p) .r-cur) (sym $ receiveMsg-qcHigh tpm)
  $ subst (_ <_)  (sym $ receiveMsg-rCur tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Committing⇒StepLocks∗ ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | Lock ph≡ (isHighest hq∈ _) | tt with IH≫ ph≡
... | mk g = g hq∈

Commit⇒QCBound : ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s)(let ls = s ＠ p) →
  ls .phase ≡ Voting
  ──────────────────────────────
  ls .qc-high ∙round < ls .r-cur
Commit⇒QCBound {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Commit⇒QCBound {p} ⦃ hp ⦄ (_ , s-init , s′ ⟨ st ∣ s ⟩←— tr) ph≡
  with Rs ← _ , s-init , tr
  with IH ← Commit⇒QCBound {p} Rs
  with IH≫ ← Lock⇒QCBound {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (λ ◆ → ◆ ∙round < (s′ ＠ p) .r-cur) (sym $ receiveMsg-qcHigh tpm)
  $ subst (_ <_)  (sym $ receiveMsg-rCur tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Voting⇒StepCommits∗ ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | Commit     ph≡ _ | tt = IH≫ ph≡
... | CommitNoOp ph≡ _ | tt = IH≫ ph≡

Vote⇒QCBound : ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s)(let ls = s ＠ p) →
  ls .phase ≡ EnteringRound
  ──────────────────────────────
  ls .qc-high ∙round < ls .r-cur
Vote⇒QCBound {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = Nat.s≤s Nat.z≤n
Vote⇒QCBound {p}  ⦃ hp ⦄ (_ , s-init , s′ ⟨ st ∣ s ⟩←— tr) ph≡
  with Rs ← _ , s-init , tr
  with IH ← Vote⇒QCBound {p} Rs
  with IH≫ ← Commit⇒QCBound {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (λ ◆ → ◆ ∙round < (s′ ＠ p) .r-cur) (sym $ receiveMsg-qcHigh tpm)
  $ subst (_ <_)  (sym $ receiveMsg-rCur tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p  ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | EnteringRound⇒StepVotes∗ ((_ ⊢ st)  ⦃ hp ⦄) ph≡
... | VoteBlock ph≡ _ _   | tt , _ = IH≫ ph≡
... | VoteBlockNoOp ph≡ _ | tt , _ = IH≫ ph≡

Init⇒QCBound : ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s)(let ls = s ＠ p) →
  ls .phase ≡ Proposing
  ──────────────────────────────
  ls .qc-high ∙round < ls .r-cur
Init⇒QCBound {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Init⇒QCBound {p} ⦃ hp ⦄ (_ , s-init , s′ ⟨ st ∣ s ⟩←— tr) ph≡
  with Rs ← _ , s-init , tr
  with IH ← Init⇒QCBound {p} Rs
  with IH≫ ← Vote⇒QCBound {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (λ ◆ → ◆ ∙round < (s′ ＠ p) .r-cur) (sym $ receiveMsg-qcHigh tpm)
  $ subst (_ <_)  (sym $ receiveMsg-rCur tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p  ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Proposing⇒StepInits ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | InitTC   ph≡ _ | tt = IH≫ ph≡
... | InitNoTC ph≡ _ | tt = IH≫ ph≡

Propose⇒QCBound : ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s)(let ls = s ＠ p) →
  ls .phase ≡ Receiving
  ──────────────────────────────
  ls .qc-high ∙round < ls .r-cur
Propose⇒QCBound {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Propose⇒QCBound {p} ⦃ hp ⦄ (_ , s-init , s′ ⟨ st ∣ s ⟩←— tr) ph≡
  with Rs ← _ , s-init , tr
  with IH ← Propose⇒QCBound {p} Rs
  with IH≫ ← Init⇒QCBound {p} Rs
  with IH≫≫ ← Commit⇒QCBound {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst (λ ◆ → ◆ ∙round < (s′ ＠ p) .r-cur) (sym $ receiveMsg-qcHigh tpm)
  $ subst (_ <_)  (sym $ receiveMsg-rCur tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p  ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st
... | ProposeBlock     ph≡ _     = IH≫ ph≡
... | ProposeBlockNoOp ph≡ _     = IH≫ ph≡
... | EnoughTimeouts   ph≡ _ _ _ = IH ph≡
... | TimerExpired     ph≡ _     = IH ph≡
... | VoteBlock        ph≡ _ _   = IH≫≫ ph≡
... | VoteBlockNoOp    ph≡ _     = IH≫≫ ph≡

-- ls .qc-high -highest-qc-∈- ls .db

Lock⇒HighestQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .phase ≡ Committing
  ──────────────────────────────────
  ls .qc-high -highest-qc-∈- ls .db
Lock⇒HighestQC {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Lock⇒HighestQC {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡
 with Rs ← _ , s-init , tr
 with IH ← Lock⇒HighestQC {p} Rs
 with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst ((s′ ＠ p) .qc-high -highest-qc-∈-_) (sym $ receiveMsg-db tpm)
  $ subst (_-highest-qc-∈- _) (sym $ receiveMsg-qcHigh tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p  ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Committing⇒StepLocks∗ ((_ ⊢ st)  ⦃ hp ⦄) ph≡
... | Lock ph≡ qc∈ | tt = qc∈

Commit⇒HighestQC : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .phase ≡ Voting
  ──────────────────────────────────
  ls .qc-high -highest-qc-∈- ls .db
Commit⇒HighestQC {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Commit⇒HighestQC {p} ⦃ hp ⦄ (_ , s-init , s′ ⟨ st ∣ s ⟩←— tr) ph≡
  with Rs ← _ , s-init , tr
  with IH ← Commit⇒HighestQC {p} Rs
  with IH≫ ← Lock⇒HighestQC {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = let tpm = honestTPMessage tpm in
    subst ((s′ ＠ p) .qc-high -highest-qc-∈-_) (sym $ receiveMsg-db tpm)
  $ subst (_-highest-qc-∈- _) (sym $ receiveMsg-qcHigh tpm)
  $ IH (subst (_≡ _) (receiveMsg-phase tpm) ph≡)
... | DishonestLocalStep _ _ = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Voting⇒StepCommits∗ ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | Commit     ph≡ _ | tt = IH≫ ph≡
... | CommitNoOp ph≡ _ | tt = IH≫ ph≡

vote-qc-high : ∀ ⦃ _ : Honest p ⦄ → (Rs : Reachable s) →
  ∙ s ▷ StepVotes p b
  ∙ b ∙round ≡ 1 + b .blockQC ∙round
    ───────────────────────────────────────────────
    (b .blockQC) ∙round ≡ ((s ＠ p) .qc-high) ∙round
vote-qc-high {p}{s}{b} ⦃ hp ⦄ Rs stepvote refl
  with b∈ ← StepVotes⇒b∈db {s = s} stepvote
  with ph≡ ← StepVotes⇒Voting {s = s} stepvote
  with (r≡ , r> , sum) ← StepVotes⇒ShouldVote′ {s = s} stepvote
  = ≤-antisym bqc≤ bqc≥
  where
  open Nat
  open Nat.≤-Reasoning renaming (begin_ to begin≤_; _∎ to _∎≤)

  bqc≤ : b .blockQC ≤qc (s ＠ p) .qc-high
  bqc≤
    with (isHighest _ <qch) ← Commit⇒HighestQC Rs ph≡
    = <qch (b .blockQC) (b∈⇒qc∈ b∈)
  {-
   Because of Stepvotes, we went through StepLock and updated qc-high,
  hence ls .qc-high ≥ b .blockQC ∙round (because b ∙∈ ls .db) and hence b .blockQC ∙∈ ls .db
  -}

  bqc≥ : (s ＠ p) .qc-high ≤qc b .blockQC
  bqc≥ = ≤-pred $ begin≤
     1 + (s ＠ p) .qc-high ∙round
    ≤⟨ Commit⇒QCBound Rs ph≡ ⟩
     (s ＠ p) .r-cur
    ≡⟨ sym r≡ ⟩
     b ∙round
    ≡⟨⟩
     1 + b .blockQC ∙round
    ∎≤
