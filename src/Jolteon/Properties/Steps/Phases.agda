{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.Phases (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.State ⋯

-- ** Relating phases to step properties.

Proposing⇒StepInits : ∀ (st : Step) →
  (st ∙end) .phase ≡ Proposing
  ────────────────────────────
  StepInits st
Proposing⇒StepInits (_ ⊢ InitTC _ _) _ = tt
Proposing⇒StepInits (_ ⊢ InitNoTC _ _) _ = tt
Proposing⇒StepInits (_ ⊢ EnoughTimeouts ph≡′ _ _ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Proposing⇒StepInits (_ ⊢ TimerExpired ph≡′ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Proposing⇒StepInits ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡
Proposing⇒StepInits ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡

Receiving⇒StepReceiving : ∀ (st : Step) → let ls = st ∙end in
  ls .phase ≡ Receiving
  ────────────────────────────
    StepReceiving st
  ⊎ ls .roundAdvanced? ≡ false
Receiving⇒StepReceiving (_ ⊢ ProposeBlock _ _) _ = inj₁ tt
Receiving⇒StepReceiving (_ ⊢ ProposeBlockNoOp _ _) _ = inj₁ tt
Receiving⇒StepReceiving (_ ⊢ EnoughTimeouts ph≡′ _ _ _) _ = inj₁ tt
Receiving⇒StepReceiving (_ ⊢ TimerExpired ph≡′ _) _ = inj₁ tt
Receiving⇒StepReceiving ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = inj₂ refl
... | true  = inj₁ $ contradict ph≡
Receiving⇒StepReceiving ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = inj₂ refl
... | true  = inj₁ $ contradict ph≡

AdvancingRound⇒StepRegisters : ∀ (st : Step) →  let ls = st ∙end in
  ls .phase ≡ AdvancingRound
  ──────────────────────────
    StepRegisters st
  ⊎ ls .roundAdvanced? ≡ true
AdvancingRound⇒StepRegisters (_ ⊢ RegisterTC _ _ _ _) _ = inj₁ tt
AdvancingRound⇒StepRegisters (_ ⊢ RegisterProposal _ _ _ _ _) _ = inj₁ tt
AdvancingRound⇒StepRegisters (_ ⊢ RegisterTimeout _ _ _ _) _ = inj₁ tt
AdvancingRound⇒StepRegisters (_ ⊢ RegisterVote _ _ _ _ _ _) _ = inj₁ tt
AdvancingRound⇒StepRegisters (_ ⊢ EnoughTimeouts ph≡′ _ _ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
AdvancingRound⇒StepRegisters (_ ⊢ TimerExpired ph≡′ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
AdvancingRound⇒StepRegisters ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡
AdvancingRound⇒StepRegisters ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡
AdvancingRound⇒StepRegisters (_ ⊢ AdvanceRoundQC _ _ _) _ = inj₂ refl
AdvancingRound⇒StepRegisters (_ ⊢ AdvanceRoundTC _ _ _) _ = inj₂ refl

AdvancingRound⇒StepAdvances* : ∀ (st : Step) →  let ls = st ∙end in
  ls .phase ≡ AdvancingRound
  ──────────────────────────
    StepAdvances* st
AdvancingRound⇒StepAdvances* (_ ⊢ RegisterProposal _ _ _ _ _) _ = tt
AdvancingRound⇒StepAdvances* (_ ⊢ RegisterVote _ _ _ _ _ _) _ = tt
AdvancingRound⇒StepAdvances* (_ ⊢ RegisterTimeout _ _ _ _) _ = tt
AdvancingRound⇒StepAdvances* (_ ⊢ RegisterTC _ _ _ _) _ = tt
AdvancingRound⇒StepAdvances* (_ ⊢ EnoughTimeouts ph≡′ _ _ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
AdvancingRound⇒StepAdvances* (_ ⊢ TimerExpired ph≡′ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
AdvancingRound⇒StepAdvances* (_ ⊢ AdvanceRoundQC _ _ _) _ = tt
AdvancingRound⇒StepAdvances* (_ ⊢ AdvanceRoundTC _ _ _) _ = tt
AdvancingRound⇒StepAdvances* ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡
AdvancingRound⇒StepAdvances* ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡

Locking⇒StepAdvances : ∀ (st : Step) →
  (st ∙end) .phase ≡ Locking
  ──────────────────────────
  StepAdvances st
Locking⇒StepAdvances (_ ⊢ AdvanceRoundNoOp _ _ _) _ = tt
Locking⇒StepAdvances (_ ⊢ EnoughTimeouts ph≡′ _ _ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Locking⇒StepAdvances (_ ⊢ TimerExpired ph≡′ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Locking⇒StepAdvances ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡
Locking⇒StepAdvances ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡

Committing⇒StepLocks∗ : ∀ (st : Step) →
  (st ∙end) .phase ≡ Committing
  ─────────────────────────────
  StepLocks∗ st
Committing⇒StepLocks∗ (_ ⊢ Lock _ _) _ = tt
Committing⇒StepLocks∗ (_ ⊢ EnoughTimeouts ph≡′ _ _ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Committing⇒StepLocks∗ (_ ⊢ TimerExpired ph≡′ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Committing⇒StepLocks∗ ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡
Committing⇒StepLocks∗ ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡

Voting⇒StepCommits∗ : ∀ (st : Step) →
  (st ∙end) .phase ≡ Voting
  ─────────────────────────
  StepCommits∗ st
Voting⇒StepCommits∗ (_ ⊢ Commit _ _) _ = tt
Voting⇒StepCommits∗ (_ ⊢ CommitNoOp _ _) _ = tt
Voting⇒StepCommits∗ (_ ⊢ EnoughTimeouts ph≡′ _ _ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Voting⇒StepCommits∗ (_ ⊢ TimerExpired ph≡′ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
Voting⇒StepCommits∗ ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡
Voting⇒StepCommits∗ ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = contradict ph≡

EnteringRound⇒StepVotes∗ : ∀ (st : Step) → let ls = st ∙end in
  ls .phase ≡ EnteringRound
  ──────────────────────────────────────
  StepVotes∗ st × T (ls .roundAdvanced?)
EnteringRound⇒StepVotes∗ (_ ⊢ EnoughTimeouts ph≡′ _ _ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
EnteringRound⇒StepVotes∗ (_ ⊢ TimerExpired ph≡′ _) ph≡ =
  contradict $ trans (sym ph≡) ph≡′
EnteringRound⇒StepVotes∗ ((_ , _ , ls , _) ⊢ VoteBlock _ _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = tt , tt
EnteringRound⇒StepVotes∗ ((_ , _ , ls , _) ⊢ VoteBlockNoOp _ _) ph≡
  with ls .roundAdvanced?
... | false = contradict ph≡
... | true  = tt , tt

-- ** Relating phases to the state's `roundAdvanced?` flag.

EnteringRound⇒roundAdvanced : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .phase ≡ EnteringRound
  ─────────────────────────
  ls .roundAdvanced? ≡ true
EnteringRound⇒roundAdvanced {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = refl
EnteringRound⇒roundAdvanced {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡
  with Rs ← _ , s-init , tr
  with IH ← EnteringRound⇒roundAdvanced {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = subst (_≡ true) (sym $ receiveMsg-roundA (honestTPMessage tpm))
  $ IH (subst (_≡ _) (receiveMsg-phase (honestTPMessage tpm)) ph≡)
... | DishonestLocalStep  _ _
  = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | (st ∙end) .roundAdvanced? | EnteringRound⇒StepVotes∗ ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | VoteBlock _ _ _   | true | tt , tt = refl
... | VoteBlockNoOp _ _ | true | tt , tt = refl

Proposing⇒¬roundAdvanced : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .phase ≡ Proposing
  ──────────────────────────
  ls .roundAdvanced? ≡ false
Proposing⇒¬roundAdvanced {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Proposing⇒¬roundAdvanced {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡
  with Rs ← _ , s-init , tr
  with IH ← Proposing⇒¬roundAdvanced {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = subst (_≡ false) (sym $ receiveMsg-roundA (honestTPMessage tpm))
  $ IH (subst (_≡ _) (receiveMsg-phase (honestTPMessage tpm)) ph≡)
... | DishonestLocalStep _ _
  = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Proposing⇒StepInits ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | InitTC _ _   | tt = refl
... | InitNoTC _ _ | tt = refl

Receiving⇒¬roundAdvanced : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .phase ≡ Receiving
  ──────────────────────────
  ls .roundAdvanced? ≡ false
Receiving⇒¬roundAdvanced {p} (_ , refl , (_ ∎)) ph≡
  rewrite pLookup-replicate p initLocalState
  = contradict ph≡
Receiving⇒¬roundAdvanced {p} ⦃ hp ⦄ (_ , s-init , (s′ ⟨ st ∣ s ⟩←— tr)) ph≡
  with Rs ← _ , s-init , tr
  with IH ← Receiving⇒¬roundAdvanced {p} Rs
  with st
... | WaitUntil _ _ _
  = IH ph≡
... | Deliver {tpm} _
  = subst (_≡ false) (sym $ receiveMsg-roundA (honestTPMessage tpm))
  $ IH (subst (_≡ _) (receiveMsg-phase (honestTPMessage tpm)) ph≡)
... | DishonestLocalStep _ _
  = IH ph≡
... | LocalStep {p = p′} {ls′ = ls′} st
  with p ≟ p′
... | no p≢ rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH ph≡
... | yes refl rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st | Receiving⇒StepReceiving ((_ ⊢ st) ⦃ hp ⦄) ph≡
... | ProposeBlock ph≡ _     | inj₁ tt = Proposing⇒¬roundAdvanced ⦃ hp ⦄ Rs ph≡
... | ProposeBlockNoOp ph≡ _ | inj₁ tt = Proposing⇒¬roundAdvanced ⦃ hp ⦄ Rs ph≡
... | EnoughTimeouts _ _ _ _ | inj₁ tt = IH ph≡
... | TimerExpired _ _       | inj₁ tt = IH ph≡
... | _                      | inj₂ r≡ = r≡

AdvancingRound⇒¬roundAdvanced : ∀ {s} → Reachable s →
  (ssr : s ▷ StepRegisters) →
  ──────────────────────────
  let (st , _ ) = ssr ; (_ , _ , _ , _ , ls′) = stepArgs st in
  ls′ .roundAdvanced? ≡ false
AdvancingRound⇒¬roundAdvanced Rs ((_ ⊢ st) , refl , refl , x)
  with st | x
... | RegisterProposal _ ph≡ _ _ _ | tt = Receiving⇒¬roundAdvanced Rs ph≡
... | RegisterVote _ ph≡ _ _ _ _ | tt =  Receiving⇒¬roundAdvanced Rs ph≡
... | RegisterTimeout _ ph≡ _ _ | tt =  Receiving⇒¬roundAdvanced Rs ph≡
... | RegisterTC _ ph≡ _ _ | tt =  Receiving⇒¬roundAdvanced Rs ph≡
