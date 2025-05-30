{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.Core (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability ⋯
open import Jolteon.Properties.State.Invariants ⋯
open import Jolteon.Properties.State.Messages ⋯

-- ** Characterizing subset of local steps

StepVotes : Pid → Block → LocalStepProperty
StepVotes p b ((_p , _) ⊢ st) = case st of λ where
  (VoteBlock {b = _b} _ _ _) → p ≡ _p × b ≡ _b
  _ → ⊥

StepVotes′ : Pid → QC → LocalStepProperty
StepVotes′ p qc ((_p , _) ⊢ st) = case st of λ where
  (VoteBlock{b = b} _ _ _) → p ≡ _p × qc ∙blockId ≡ b ∙blockId × qc ∙round ≡ b ∙round
  _ → ⊥


StepCommits : Block → LocalStepProperty
StepCommits b (_ ⊢ st) = case st of λ where
  (Commit _ (final∈ {b = _b} _ _ _ _ , _)) → b ≡ _b
  _ → ⊥

StepCommits∈ : Block → LocalStepProperty
StepCommits∈ b (_ ⊢ st) = case st of λ where
  (Commit {ch = ch} _ _) → b ∈ ch
  _ → ⊥

StepCommitsRound> : Pid → Round → LocalStepProperty
StepCommitsRound> p r ((_p , _) ⊢ st) = case st of λ where
  (Commit _ (final∈ {b = _b} _ _ _ _ , _)) → p ≡ _p × r < _b ∙round
  _ → ⊥

StepProposes : Block → LocalStepProperty
StepProposes b ((_ , _ , ls , _) ⊢ st) = case st of λ where
  (ProposeBlock {txn = txn} _ _) → b ≡ mkBlockForState ls txn
  _ → ⊥

StepLocks : Pid → QC → LocalStepProperty
StepLocks p qc ((_p , _) ⊢ st) = case st of λ where
  (Lock {qc = _qc} _ _) → p ≡ _p × qc ≡ _qc
  _ → ⊥

StepAdvancesQC : Pid → QC → LocalStepProperty
StepAdvancesQC p qc ((_p , _) ⊢ st) = case st of λ where
  (AdvanceRoundQC {qc = _qc} _ _ _) → p ≡ _p × qc ≡ _qc
  _ → ⊥

StepInitsTC : TC → LocalStepProperty
StepInitsTC tc ((_ , _ , _ , _) ⊢ st) = case st of λ where
  (InitTC {tc = _tc} _ _) → tc ≡ _tc
  _ → ⊥

StepTimeout : Pid → TimeoutEvidence → LocalStepProperty
StepTimeout p te ((_p , _ , ls , _) ⊢ st) =
  let P = p ≡ _p × te ≡ signData p (ls .r-cur , ls .qc-high) in
  case st of λ where
  (TimerExpired _ _) → P
  (EnoughTimeouts _ _ _ _) → P
  _ → ⊥

StepRegisterProposal : Pid → Proposal → LocalStepProperty
StepRegisterProposal p sb ((_p , _ , _ , _) ⊢ st) =  case st of λ where
  (RegisterProposal {sb = _sb} _ _ _ _ _) → p ≡ _p × sb ≡ _sb
  _ → ⊥

StepInits StepReceiving StepRegisters StepAdvancesLoop StepAdvances StepAdvances* StepLocks∗ StepCommits∗ StepVotes∗
  : LocalStepProperty
StepInits (_ ⊢ st) = case st of λ where
  (InitTC _ _) → ⊤
  (InitNoTC _ _) → ⊤
  _ → ⊥
StepReceiving (_ ⊢ st) = case st of λ where
  (ProposeBlock _ _) → ⊤
  (ProposeBlockNoOp _ _) → ⊤
  (EnoughTimeouts _ _ _ _) → ⊤
  (TimerExpired _ _) → ⊤
  _ → ⊥
StepRegisters (_ ⊢ st) = case st of λ where
  (RegisterTC _ _ _ _) → ⊤
  (RegisterProposal _ _ _ _ _) → ⊤
  (RegisterTimeout _ _ _ _) → ⊤
  (RegisterVote _ _ _ _ _ _) → ⊤
  _ → ⊥

StepAdvancesLoop (_ ⊢ st) = case st of λ where
  (AdvanceRoundQC _ _ _) → ⊤
  (AdvanceRoundTC _ _ _) → ⊤
  _ → ⊥

StepAdvances* (_ ⊢ st) = case st of λ where
  (RegisterTC _ _ _ _) → ⊤
  (RegisterProposal _ _ _ _ _) → ⊤
  (RegisterTimeout _ _ _ _) → ⊤
  (RegisterVote _ _ _ _ _ _) → ⊤
  (AdvanceRoundQC _ _ _) → ⊤
  (AdvanceRoundTC _ _ _) → ⊤
  _ → ⊥


StepAdvances (_ ⊢ st) = case st of λ where
  (AdvanceRoundNoOp _ _ _) → ⊤
  _ → ⊥
StepLocks∗ (_ ⊢ st) = case st of λ where
  (Lock _ _) → ⊤
  _ → ⊥
StepCommits∗ (_ ⊢ st) = case st of λ where
  (Commit _ _) → ⊤
  (CommitNoOp _ _) → ⊤
  _ → ⊥
StepVotes∗ (_ ⊢ st) = case st of λ where
  (VoteBlock _ _ _) → ⊤
  (VoteBlockNoOp _ _) → ⊤
  _ → ⊥

-- ** Decidability of step properties

StepVotes? : ∀ p b st → Dec (StepVotes p b st)
StepVotes? p b ((_p , _) ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock {b = _b} _ _ _ = ¿ p ≡ _p × b ≡ _b ¿
... | VoteBlockNoOp _ _ = no λ ()

StepVotes′? : ∀ p qc st → Dec (StepVotes′ p qc st)
StepVotes′? p qc ((_p , _) ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock {b = b} _ _ _ = ¿ p ≡ _p × qc ∙blockId ≡ b ∙blockId × qc ∙round ≡ b ∙round ¿
... | VoteBlockNoOp _ _ = no λ ()

StepCommits? : Decidable² StepCommits
StepCommits? b (_ ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ (final∈ {b = _b} _ _ _ _ , _) = b ≟ _b
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

StepCommitsRound? : ∀ p r st → Dec (StepCommitsRound> p r st)
StepCommitsRound? p r ((_p , _ ) ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ (final∈ {b = _b} _ _ _ _ , _) = ¿ p ≡ _p × r < _b ∙round ¿
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

StepCommits∈? : Decidable² StepCommits∈
StepCommits∈? b (_ ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit {ch = ch} _ _ = b ∈? ch
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

StepProposes? : Decidable² StepProposes
StepProposes? b ((_ , _ , ls , _ ) ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock {txn = txn} _ _ = b ≟ mkBlockForState ls txn
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

StepLocks? : ∀ x y z → Dec (StepLocks x y z)
StepLocks? p qc ((_p , _ , ls , _ ) ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock {qc = _qc} _ _ = ¿ p ≡ _p × qc ≡ _qc ¿
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

StepAdvancesQC? : ∀ x y z → Dec (StepAdvancesQC x y z)
StepAdvancesQC? p qc ((_p , _ , ls , _ ) ⊢ st) with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC {qc = _qc} _ _ _ = ¿ p ≡ _p × qc ≡ _qc ¿
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()


StepInitsTC? : Decidable² StepInitsTC
StepInitsTC? tc ((_ , _ , ls , _ ) ⊢ st) with st
... | InitTC {tc = _tc} _ _ = tc ≟ _tc
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

StepInits? : Decidable¹ StepInits
StepInits? (_ ⊢ st) with st
... | InitTC _ _ = yes tt
... | InitNoTC _ _ = yes tt
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = no λ ()
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = no λ ()
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

StepTimeout? : ∀ p te st → Dec (StepTimeout p te st)
StepTimeout? p te ((_p , _ , ls , _) ⊢ st)
  with P? ← ¿ p ≡ _p × te ≡ signData p (ls .r-cur , ls .qc-high) ¿
  with st
... | InitTC _ _ = no λ ()
... | InitNoTC _ _ = no λ ()
... | ProposeBlock _ _ = no λ ()
... | ProposeBlockNoOp _ _ = no λ ()
... | RegisterProposal _ _ _ _ _ = no λ ()
... | EnoughTimeouts _ _ _ _ = P?
... | RegisterTimeout _ _ _ _ = no λ ()
... | RegisterTC _ _ _ _ = no λ ()
... | TimerExpired _ _ = P?
... | RegisterVote _ _ _ _ _ _ = no λ ()
... | AdvanceRoundQC _ _ _ = no λ ()
... | AdvanceRoundTC _ _ _ = no λ ()
... | AdvanceRoundNoOp _ _ _ = no λ ()
... | Lock _ _ = no λ ()
... | Commit _ _ = no λ ()
... | CommitNoOp _ _ = no λ ()
... | VoteBlock _ _ _ = no λ ()
... | VoteBlockNoOp _ _ = no λ ()

-- ** Simple proofs about step properties.

StepVotes⇒ShouldVote : ∀ {s} (Rs : Reachable s) →
  Rs ∋⋯ StepVotes p b
  ────────────────────────
  ∃ λ ls → ShouldVote ls b
StepVotes⇒ShouldVote (s , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) st∈
  = StepVotes⇒ShouldVote (s , s-init , tr) st∈
StepVotes⇒ShouldVote (s , s-init , (_ ⟨ Deliver _ ⟩←— tr)) st∈
  = StepVotes⇒ShouldVote (s , s-init , tr) st∈
StepVotes⇒ShouldVote (s , s-init , (_ ⟨ DishonestLocalStep _ _ ⟩←— tr)) st∈
  = StepVotes⇒ShouldVote (s , s-init , tr) st∈
StepVotes⇒ShouldVote (s , s-init , (_ ⟨ LocalStep p ⟩←— tr))
  (there st∈)
  = StepVotes⇒ShouldVote (s , s-init , tr) st∈
StepVotes⇒ShouldVote (_ , _ , (_ ⟨ LocalStep {p = p} (VoteBlock _ _ sv) ∣ s ⟩←— tr))
  (here (refl , refl))
  = s ＠ p , sv

StepVotes⇒ShouldVote′ : ⦃ _ : Honest p ⦄ →
  s ▷ StepVotes p b
  ────────────────────
  ShouldVote (s ＠ p) b
StepVotes⇒ShouldVote′ (_ ⊢ VoteBlock _ _ sv , refl , refl , refl , refl) = sv

StepVotes⇒r≡ : ⦃ _ : Honest p ⦄ →
  StepVotes p b ◃ s
  ──────────────────────────
  b ∙round ≡ (s ＠ p) .r-vote
StepVotes⇒r≡ {p} ⦃ hp ⦄
  ((_ , _ , _ , _ , ls′) ⊢ VoteBlock _ _ (refl , _) , s , refl , refl , refl , refl , refl)
  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  = refl

StepVotes⇒Voting : ⦃ _ : Honest p ⦄ →
  s ▷ StepVotes p b
  ───────────────────────
  (s ＠ p) .phase ≡ Voting
StepVotes⇒Voting (_ ⊢ VoteBlock ph _ _ , _ , refl , refl , _) = ph

StepVotes⇒b∈db : ⦃ _ : Honest p ⦄ →
  s ▷ StepVotes p b
  ─────────────────
  b ∙∈ (s ＠ p) .db
StepVotes⇒b∈db (_ ⊢ VoteBlock _ b∈ _ , refl , refl , refl , refl) = b∈

StepProposes⇒b∈ : ∀ {s} (Rs : Reachable s) →
  Rs ∋⋯ StepProposes b
  ─────────────────────────
  b ∙∈ s .history
StepProposes⇒b∈ (s , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) st∈
  = StepProposes⇒b∈ (s , s-init , tr) st∈
StepProposes⇒b∈ (s , s-init , (_ ⟨ Deliver _ ⟩←— tr)) st∈
  = StepProposes⇒b∈ (s , s-init , tr) st∈
StepProposes⇒b∈ (_ , s-init , (_ ⟨ DishonestLocalStep {env} _ _ ∣ s ⟩←— tr)) st∈
  = ∈-allBlocks-there {ms = s .history} {m = env .content}
  $ StepProposes⇒b∈ (_ , s-init , tr) st∈
StepProposes⇒b∈ (s , s-init , (_ ⟨ LocalStep {menv = me} p ⟩←— tr)) (there st∈)
  = ∈-allBlocks⁺ʳ {ms = L.fromMaybe (M.map _∙message me)}
  $ StepProposes⇒b∈ (s , s-init , tr) st∈
StepProposes⇒b∈ (_ , _ , (_ ⟨ LocalStep (ProposeBlock _ _) ⟩←— _)) (here px)
  = here px

{- NOT TRUE with Adversarial behaviour
b∈⇒StepProposes : ∀ {s} (Rs : Reachable s) →
  b ∙∈ s .history
  ────────────────────
  Rs ∋⋯ StepProposes b
b∈⇒StepProposes (_ , refl , (_ ∎)) b∈
  = contradict b∈
b∈⇒StepProposes (s , s-init , (_ ⟨ Deliver _ _ _ ⟩←— tr)) b∈
  = b∈⇒StepProposes (s , s-init , tr) b∈
b∈⇒StepProposes (s , s-init , (_ ⟨ DishonestLocalStep {env} _ _ ⟩←— tr)) b∈
  = {!!}
-- b∈⇒StepProposes (s , s-init , (_ ⟨ DishonestLocalStep {env} _ _ ⟩←— tr)) (here px)
--   = ?
-- b∈⇒StepProposes (s , s-init , (_ ⟨ DishonestLocalStep {env} _ _ ⟩←— tr)) (there b∈)
--   = b∈⇒StepProposes (s , s-init , tr) b∈
b∈⇒StepProposes {b} (_ , s-init , (_ ⟨ LocalStep st ⟩←— tr)) b∈
  with IH ← b∈⇒StepProposes {b} (_ , s-init , tr)
  with st
... | InitNoTC _ _
  = there $ IH b∈
... | ProposeBlockNoOp _ _
  = there $ IH b∈
... | RegisterProposal _ _ _ _ _
  = there $ IH b∈
... | RegisterVote _ _ _ _ _ _
  = there $ IH b∈
... | RegisterTimeout _ _ _ _
  = there $ IH b∈
... | RegisterTC _ _ _ _
  = there $ IH b∈
... | AdvanceRoundQC _ _ _
  = there $ IH b∈
... | AdvanceRoundTC _ _ _
  = there $ IH b∈
... | AdvanceRoundNoOp _ _ _
  = there $ IH b∈
... | Lock _ _
  = there $ IH b∈
... | Commit _ _
  = there $ IH b∈
... | CommitNoOp _ _
  = there $ IH b∈
... | VoteBlockNoOp _ _
  = there $ IH b∈
... | InitTC {tc = tc} _ _
  = there $ IH b∈
... | EnoughTimeouts _ _ _ _
  = there $ IH b∈
... | TimerExpired _ _
  = there $ IH b∈
... | VoteBlock _ _ _
  = there $ IH b∈
... | ProposeBlock {txn = txn} _ _
  with b∈
... | here  b≡ = here b≡
... | there b∈ = there $ IH b∈
-}

sb∈⇒StepRegisterProposal : ∀ {s} ⦃ _ : Honest p ⦄ → (Rs : Reachable s) →
  Propose sb ∈ (s ＠ p) .db
  ───────────────────────────────
  Rs ∋⋯ StepRegisterProposal p sb
sb∈⇒StepRegisterProposal {p = p} (_ , refl , (_ ∎)) pr∈
  rewrite pLookup-replicate p initLocalState
  = contradict pr∈
sb∈⇒StepRegisterProposal {p}{sb} ⦃ hp ⦄ (_ , s-init , _ ⟨ st ∣ s ⟩←— tr) pr∈
  -- with Rs ← _ , s-init , tr
  with IH ← sb∈⇒StepRegisterProposal {p}{sb} ⦃ hp ⦄ (_ , s-init , tr)
  with st
... | WaitUntil _ _ _
  = IH pr∈
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p = p}{s .stateMap} (honestTPMessage tpm)
  = IH pr∈
... | DishonestLocalStep _ _
  = IH pr∈
... | LocalStep {p = p′}{ls′ = ls′} st
  with lookup✓ ← pLookup∘updateAt p {const ls′} (s .stateMap)
  with lookup✖ ← (λ p≢ → pLookup∘updateAt′ p p′ {const ls′} p≢ (s .stateMap))
  with p ≟ p′
... | no p≢ rewrite lookup✖ (p≢ ∘ ↑-injective) = there $ IH pr∈
... | yes refl
  rewrite lookup✓
  with st
... | InitNoTC _ _
  = there $ IH pr∈
... | ProposeBlockNoOp _ _
  = there $ IH pr∈
... | RegisterVote _ _ _ _ _ _
  with there pr∈ ← pr∈
  = there $ IH pr∈
... | RegisterTimeout _ _ _ _
  with there pr∈ ← pr∈
  = there $ IH pr∈
... | RegisterTC _ _ _ _
  with there pr∈ ← pr∈
  = there $ IH pr∈
... | AdvanceRoundQC _ _ _
  = there $ IH pr∈
... | AdvanceRoundTC _ _ _
  = there $ IH pr∈
... | AdvanceRoundNoOp _ _ _
  = there $ IH pr∈
... | Lock _ _
  = there $ IH pr∈
... | Commit _ _
  = there $ IH pr∈
... | CommitNoOp _ _
  = there $ IH pr∈
... | VoteBlockNoOp _ _
  = there $ IH pr∈
... | InitTC {tc = tc} _ _
  = there $ IH pr∈
... | EnoughTimeouts _ _ _ _
  = there $ IH pr∈
... | TimerExpired _ _
  = there $ IH pr∈
... | VoteBlock _ _ _
  = there $ IH pr∈
... | ProposeBlock {txn = txn} _ _
  = there $ IH pr∈
... | RegisterProposal _ _ _ _ _
  with pr∈
... | here refl = here (refl , refl)
... | there pr∈ = there $ IH pr∈


StepRegisterProposal⇒sbValid : ∀ {s} (Rs : Reachable s) →
  Rs ∋⋯ StepRegisterProposal p sb
  ─────────────────────────────────────────
  sb .node ≡ roundLeader (sb .datum ∙round)
StepRegisterProposal⇒sbValid (s , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) st∈
  = StepRegisterProposal⇒sbValid (s , s-init , tr) st∈
StepRegisterProposal⇒sbValid (s , s-init , (_ ⟨ Deliver _ ⟩←— tr)) st∈
  = StepRegisterProposal⇒sbValid (s , s-init , tr) st∈
StepRegisterProposal⇒sbValid (s , s-init , (_ ⟨ DishonestLocalStep _ _ ⟩←— tr)) st∈
  = StepRegisterProposal⇒sbValid (s , s-init , tr) st∈
StepRegisterProposal⇒sbValid (s , s-init , (_ ⟨ LocalStep p ⟩←— tr))
  (there st∈)
  = StepRegisterProposal⇒sbValid (s , s-init , tr) st∈
StepRegisterProposal⇒sbValid (_ , _ , (_ ⟨ LocalStep {p = p} (RegisterProposal _ _ _ L≡ _) ∣ s ⟩←— tr))
  (here (refl , refl))
  = L≡

StepRegisterProposal⇒ValidProposal : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s →
  s ▷ StepRegisterProposal p sb
  ───────────────────────────────────────
  ValidProposal ((s ＠ p) .db) (sb .datum)
StepRegisterProposal⇒ValidProposal Rs
  (_ ⊢ RegisterProposal _ _ _ _ vp , refl , refl , refl , refl) = vp

StepRegisterProposal⇒ValidBlock : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s →
  s ▷ StepRegisterProposal p sb
  ─────────────────────────────
  ValidBlock (sb .datum)
StepRegisterProposal⇒ValidBlock Rs rp
  = ValidProposal⇒ValidBlock $ StepRegisterProposal⇒ValidProposal Rs rp

timeout-r-cur : ∀ {s te} → ⦃ _ : Honest p ⦄ →
  StepTimeout p te ◃ s
  ──────────────────────────
  te ∙round ≡ (s ＠ p) .r-cur
timeout-r-cur ⦃ hp ⦄ ((p , _ , _ , _ , ls′) ⊢ EnoughTimeouts _ _ _ _ , s , _ , refl , refl , refl , refl)
  rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′} (s .stateMap)
  = refl
timeout-r-cur ⦃ hp ⦄ ((p , _ , _ , _ , ls′) ⊢ TimerExpired _ _ , s , _ , refl , refl , refl , refl )
  rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′} (s .stateMap)
  = refl

timeout-qc-high : ∀ {s te} → ⦃ _ : Honest p ⦄ →
  StepTimeout p te ◃ s
  ───────────────────────────
  te ∙qcTE ≡ (s ＠ p) .qc-high
timeout-qc-high ⦃ hp ⦄ ((p , _ , _ , _ , ls′) ⊢ EnoughTimeouts _ _ _ _ , s , _ , refl , refl , refl , refl)
  rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′} (s .stateMap)
  = refl
timeout-qc-high ⦃ hp ⦄ ((p , _ , _ , _ , ls′) ⊢ TimerExpired _ _ , s , _ , refl , refl , refl , refl )
  rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′} (s .stateMap)
  = refl

-- a p step cannot send a p′ message
ownMessage :
  (p ⦂ s .currentTime ⊢ ls — menv —→ ls′)
  ───────────────────────────────────────────
  All (All (_≡ p) ∘ _∙sender? ∘ content) menv
ownMessage (InitTC _ _) = just nothing
ownMessage (InitNoTC _ _) = nothing
ownMessage (ProposeBlock _ refl) = just (just refl)
ownMessage (ProposeBlockNoOp _ _) = nothing
ownMessage (RegisterProposal _ _ _ _ _) = nothing
ownMessage (RegisterVote _ _ _ _ _ _) = nothing
ownMessage (RegisterTimeout _ _ _ _) = nothing
ownMessage (RegisterTC _ _ _ _) = nothing
ownMessage (EnoughTimeouts _ _ _ _) = just (just refl)
ownMessage (TimerExpired _ _) = just (just refl)
ownMessage (AdvanceRoundQC _ _ _) = nothing
ownMessage (AdvanceRoundTC _ _ _) = nothing
ownMessage (AdvanceRoundNoOp _ _ _) = nothing
ownMessage (Lock _ _) = nothing
ownMessage (Commit _ _) = nothing
ownMessage (CommitNoOp _ _) = nothing
ownMessage (VoteBlock _ _ _) = just (just refl)
ownMessage (VoteBlockNoOp _ _) = nothing

{-
timeout-phase : ∀ {s te} → ⦃ _ : Honest p ⦄ →
  s ▷ StepTimeout p te
  ──────────────────────────
  (s ＠ p) .phase ≡ Receiving
timeout-phase (_ ⊢ EnoughTimeouts ph _ _ _ , _ , refl , refl , refl) = ph
timeout-phase (_ ⊢ TimerExpired ph _ , _ , refl , refl , refl ) = ph
-}
