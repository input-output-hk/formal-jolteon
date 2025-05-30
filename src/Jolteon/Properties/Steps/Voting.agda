{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.Voting (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Global.NoForging ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Votes ⋯

{-
StepVotes⇒StepProposes : ∀ {s} (Rs : Reachable s) →
  Rs ∋⋯ StepVotes p b
  ────────────────────
  Rs ∋⋯ StepProposes b
StepVotes⇒StepProposes {p}{b} Rs stv
  with trE , stv▷ ← traceRs▷ Rs stv
  = let
     open TraceExtension trE
     sᵢ = intState
     Rsᵢ = reachable′

     b∈ : b ∙∈ sᵢ .history
     b∈ = b-db⊆history Rsᵢ (StepVotes⇒b∈db {sᵢ} stv▷)

    in b∈⇒StepProposes Rs (b-history-mono extension b∈)
-}

private
  MessageVote⇒StepVotes′ : ∀ {r m} → ⦃ _ : Honest p ⦄ →
      (st : p ⦂ s .currentTime ⊢ ls — just [ r ?∣ m ⟩ —→ ls′) →
    ∙ (Vote (qc .payload signed-by p) ≡ m)
      ──────────────────────────────────────────────────────────
      StepVotes′ p qc (_ ⊢ st)
  MessageVote⇒StepVotes′ (VoteBlock _ _ _) refl = refl , refl , refl

  Vote∈⇒StepVotes′ :  ∀ {s} (Rs : Reachable s) → let ms = s .history in
    ∙ Honest p
    ∙ qc ∙blockId ≢ genesisId
    ∙ Vote (qc .payload signed-by p) ∈ ms
      ───────────────────────────────────
      Rs ∋⋯ StepVotes′ p qc
  Vote∈⇒StepVotes′ {p} {qc} (_ , refl , (_ ∎)) hp _ ()
  Vote∈⇒StepVotes′ {p} {qc} (_ , s-init , (_ ⟨ st ∣ s ⟩←— tr)) hp qc≢ v∈
    with IH ← Vote∈⇒StepVotes′ {p} {qc} (_ , s-init , tr) hp qc≢
    with st
  ... | WaitUntil _ _ _  = IH v∈
  ... | Deliver _  = IH v∈
  ... | DishonestLocalStep _ nsf = IH v∈⟪
    where
    _vs = qc .payload signed-by p

    Rs : Reachable s
    Rs =  (_ , s-init , tr)

    v∈⟪ : Vote _vs ∈ (s .history)
    v∈⟪ with ⟫ v∈
    ... | ⟫ there v∈  = v∈
    ... | ⟫ here refl = vs∈ᴹ⇒vs∈ Rs ⦃ hp ⦄ refl qc≢
                      $ nsf _vs ∈-Vote hp
  ... | LocalStep {p = p′}{menv = menv} st
    with StepVotes′? p qc (_ ⊢ st)
  ... | yes stv = here stv
  ... | no ¬stv
    with menv
  ... | nothing = there $ IH v∈
  ... | just env
    with p ≟ p′
  ... | yes refl = there $ IH $
    L.Any.tail (λ where refl → ¬stv $ MessageVote⇒StepVotes′ {s = s} st refl) v∈
  ... | no p≢
    with v∈
  ... | there v∈ = there $ IH v∈
  ... | here refl = ⊥-elim $ p≢ $ M.All.drop-just $ M.All.drop-just $ ownMessage {s = s} st

  StepVotes′∈⇒b :  ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s) → let ms = s .history in
      Rs ∋⋯ StepVotes′ p qc
      ──────────────────────────────────────
      Σ Block λ b → b ∙∈ ms
                  × qc ∙blockId ≡ b ∙blockId
                  × qc ∙round ≡ b ∙round

  StepVotes′∈⇒b {p}{qc}{s} ⦃ hp ⦄ Rs stv′
   with trE , _ ⊢ st , _ , refl , px ← traceRs▷ Rs stv′
   with st | px
  ... | VoteBlock {b} _ b∈ᵢ _ | refl , id≡ , r≡ =
    let
      open TraceExtension trE

      b∈  : b ∙∈ s .history
      b∈  = b-history-mono {s = intState} extension $ b-db⊆history {p}{b}{intState} ⦃ hp ⦄ reachable′ b∈ᵢ

    in b , b∈ , id≡ , r≡

qc∈⇒b∈ : ∀ {s} (Rs : Reachable s) →
  ∙ qc ∙blockId ≢ genesisId
  ∙ qc ∙∈ s .history
    ─────────────────────────────
    Σ Block λ b →
        b ∙∈ s .history
      × qc ∙blockId ≡ b ∙blockId
      × qc ∙round   ≡ b ∙round
qc∈⇒b∈ {qc = qc}{s} Rs qc≢ qc∈ = let
  _p , p∈ , hp = qc⇒hp qc

  vs : VoteShare
  vs = qc .payload signed-by _p

  v∈ : Vote vs ∈ s .history
  v∈ = qc⇒Vote ⦃ hp ⦄ Rs qc≢ qc∈ p∈

 in StepVotes′∈⇒b {qc = qc} ⦃ hp ⦄ Rs (Vote∈⇒StepVotes′ {qc = qc} Rs hp qc≢ v∈)

StepVotes⇒db∋ : ∀ {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s) →
  let mᵖ = Propose $ b signed-by roundLeader (b ∙round) in
  Rs ∋⋯ StepVotes p b
  ───────────────────
  mᵖ ∈ (s ＠ p) .db
StepVotes⇒db∋ {p}{b} ⦃ hp ⦄ (_ , s-init , s′ ⟨ st ∣ s ⟩←— tr) stv
  with IH ← StepVotes⇒db∋ {p}{b} (_ , s-init , tr)
  with st
... | WaitUntil _ _ _
  = IH stv
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p}{s .stateMap} (honestTPMessage tpm)
  = IH stv
... | DishonestLocalStep _ _ = IH stv
... | LocalStep {p = p′} {ls′ = ls′} st
  with stv
... | here px
  = QED
  where
  QED : _ ∈ (s′ ＠ p) .db
  QED
    with ⟫ st | ⟫ px
  ... | ⟫ VoteBlock _ b∈ sv | ⟫ refl , refl
      rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
      = subst (λ ◆ → Propose (b signed-by ◆) ∈ _) l≡ m∈
      where
      ∃m∈ : ∃ λ l → Propose (b signed-by l) ∈ (ls′ .db)
      ∃m∈ with (_ signed-by l , sb∈ , refl) ← ∈-allBlocks⁻ {ms = ls′ .db} b∈
        =  l , ∈-allSBlocks⁻ sb∈
      l  = proj₁ ∃m∈
      m∈ = proj₂ ∃m∈

      Rs : Reachable s
      Rs = (_ , s-init , tr)

      l≡ : l ≡ roundLeader (b ∙round)
      l≡ = StepRegisterProposal⇒sbValid Rs (sb∈⇒StepRegisterProposal ⦃ hp ⦄ Rs m∈)
... | there stv
  with IH ← IH stv
  with lookup✓ ← pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with lookup✖ ← (λ p≢ → pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap))
  with p ≟ p′
... | no p≢ rewrite lookup✖ p≢ = IH
... | yes refl
  rewrite lookup✓
  with st
... | InitTC _ _ = IH
... | InitNoTC _ _ = IH
... | ProposeBlock _ _ = IH
... | ProposeBlockNoOp _ _ = IH
... | RegisterProposal _ _ _ _ _ = there IH
... | EnoughTimeouts _ _ _ _ = IH
... | RegisterTimeout _ _ _ _ = there IH
... | RegisterTC _ _ _ _ = there IH
... | TimerExpired _ _ = IH
... | RegisterVote _ _ _ _ _ _ = there IH
... | AdvanceRoundQC _ _ _ = IH
... | AdvanceRoundTC _ _ _ = IH
... | AdvanceRoundNoOp _ _ _ = IH
... | Lock _ _ = IH
... | Commit _ _ = IH
... | CommitNoOp _ _ = IH
... | VoteBlock _ _ _ = IH
... | VoteBlockNoOp _ _ = IH

{-
ancestor∈history : ∀ {s} → Reachable s → let ms = s .history in
  ∙ b ←— b′
  ∙ b′ ∙∈ ms
    ────────
    b ∙∈ ms

ancestor∈history (_ , refl , (_ ∎)) _ ()
ancestor∈history (_ , s-init , (_ ⟨ Deliver _ _ _ ⟩←— tr))
  b← b∈′
  = ancestor∈history (_ , s-init , tr) b← b∈′
ancestor∈history {b}{b′}
  (s₀ , s-init , (s' ⟨ LocalStep {p = p} {menv = menv} {ls′ = ls′} st ∣ s ⟩←— tr))
  b← b∈′
  with Rs ← _ , s-init , tr
  with IH ← ancestor∈history {b}{b′} Rs b←
  with st
... | InitTC _ _ = IH b∈′
... | InitNoTC _ _ = IH b∈′
... | ProposeBlockNoOp _ _ = IH b∈′
... | RegisterProposal _ _ _ _ _ = IH b∈′
... | EnoughTimeouts _ _ _ _ = IH b∈′
... | RegisterTimeout _ _ _ _ = IH b∈′
... | RegisterTC _ _ _ _ = IH b∈′
... | TimerExpired _ _ = IH b∈′
... | RegisterVote _ _ _ _ _ _ = IH b∈′
... | AdvanceRoundQC _ _ _ = IH b∈′
... | AdvanceRoundTC _ _ _ = IH b∈′
... | AdvanceRoundNoOp _ _ _ = IH b∈′
... | Lock _ _ = IH b∈′
... | CommitNoOp _ _ = IH b∈′
... | VoteBlock _ _ _ = IH b∈′
... | VoteBlockNoOp _ _ = IH b∈′
... | Commit _ _ = IH b∈′
... | ProposeBlock _ _
  with b∈′
... | there b∈′ = there $ IH b∈′
  -- we are proposing b′
... | here refl = there b∈
  where
  ≪qc∈ : (s ＠ p) .qc-high ∙∈ (s ＠ p) .db
  ≪qc∈ = qc-high∈db Rs

  qc∈ : (s ＠ p) .qc-high ∙∈ s .history
  qc∈ = qc-db⊆history Rs ≪qc∈

  ¬qc₀ : (s ＠ p) .qc-high ≢ qc₀
  ¬qc₀ qc≡ = ⊥-elim $ ¬certified-by-qc₀ (certified-by-trans qc≡ b←)

  b∈ : b ∙∈ s .history
  b∈ with _b , b∈ , id≡ , r≡ ← qc∈⇒b∈ Rs ¬qc₀ qc∈
    = subst (_∙∈ s .history) (_b ≡ b ∋ ♯-inj (trans (sym id≡) (b← .proj₁))) b∈
-}
