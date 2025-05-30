{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.Timeouts (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Global.NoForging ⋯
open import Jolteon.Properties.State ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.Steps.RCur ⋯

mutual
  telast∈ᴹ⇒te∈ : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
    ∙ te .node ≡ p
    ∙ (s ＠ p′) .tc-last ≡ just tc
    ∙ (RQ ∶ te -∈-TC- tc)
      ───────────────────────────
      te ∙∈ s .history
  telast∈ᴹ⇒te∈ {p}{p′}{te}{tc}{s} Rs te≡ tc≡ te∈
    = te∈ᴹ⇒te∈ Rs te≡ te∈′
    where
    -- te∈ : te -∈-TC- tc

    tc∈ : tc ∙∈ s .history
    tc∈ = M.All.drop-just $ subst (All _) tc≡ $ tc-last∈history Rs

    te∈′ : Any (RQ ∶ te -∈ᴹ-_) (s .history)
    te∈′
      with tc∈
    ... | receivedTC tc∈ = L.Any.map tc∈m⇒te∈m tc∈
      where
      tc∈m⇒te∈m : ∀ {m} → tc tc∈-Message m → te -∈ᴹ- m
      tc∈m⇒te∈m = λ where
        (tc∈-Propose refl) → ∈-Propose-TC (just te∈)
        (tc∈-TCFormed)     → ∈-TCFormed te∈
        (tc∈-Timeout refl) → ∈-Timeout-TC (just te∈)
    ... | formedTC ftc
      with ⟫ ∈-TC te∈ ← ⟫ te∈
      with te∈ ← te ∈ tc .tes
               ∋ L.Any.map (λ where ∈-TE → refl) te∈
      with mtc , tc∈ ← te -te-∈- s .history
                     ∋ L.All.lookup ftc te∈
      = L.Any.map (λ where refl → ∈-Timeout-TE ∈-TE) tc∈

  te∈ᴹ⇒te∈ : ∀ {s} → Reachable s → ⦃ Honest p ⦄ →
    ∙ te .node ≡ p
    ∙ Any (RQ ∶ te -∈ᴹ-_) (s .history)
      ────────────────────────────────
      te ∙∈ s .history
  te∈ᴹ⇒te∈ (_ , refl , (_ ∎)) ⦃ hp ⦄ _ ()
  te∈ᴹ⇒te∈ {p}{te} (_ , s-init , (_ ⟨ st ∣ s ⟩←— tr)) ⦃ hp ⦄ te≡ te∈
    with Rs ← _ , s-init , tr
    with IH ← te∈ᴹ⇒te∈ {p}{te} Rs te≡
    with IHₗ ← (λ {p′} ⦃ _ : Honest p′ ⦄ {tc} → telast∈ᴹ⇒te∈ {p}{p′}{te}{tc} Rs te≡)
    with st
  ... | WaitUntil _ _ _ = IH te∈
  ... | Deliver _ = IH te∈
  ... | DishonestLocalStep {env = env} {p = p′} ¬hp′ ¬frg
    = te∈-monotonic QED
    where
    QED : te ∙∈ s .history
    QED with ⟫ te∈
    ... | ⟫ there te∈ = IH te∈
    ... | ⟫ here te∈M = IH $ ¬frg te te∈M (subst Honest (sym te≡) hp)
  ... | LocalStep {p = p} {ls′ = ls′} st
    with st
  ... | InitTC {tc = tc′} _ tc≡ = te∈-monotonic QED
    where
    QED : te ∙∈ s .history
    QED with ⟫ te∈
    ... | ⟫ there te∈ = IH te∈
    ... | ⟫ here (∈-TCFormed (∈-TC te∈tc′)) = telast∈ᴹ⇒te∈ Rs te≡ tc≡ (∈-TC te∈tc′)
  ... | InitNoTC _ _ = IH te∈
  ... | ProposeBlock {txn = txn} _ _ = te∈-monotonic QED
    where
    QED : te ∙∈ s .history
    QED with ⟫ te∈
    ... | ⟫ there te∈ = IH te∈
    ... | ⟫ here (∈-Propose-TC te∈tc) =
      let tc , tc≡ = destruct-Is-just $ Any⇒Is-just te∈tc
      in  telast∈ᴹ⇒te∈ Rs te≡ tc≡ (Any-just tc≡ te∈tc)
  ... | ProposeBlockNoOp _ _ = IH te∈
  ... | EnoughTimeouts _ _ _ _ = QED
    where
    _ls = s ＠ p
    _m = Timeout $ signData p (_ls .r-cur , _ls .qc-high) , _ls .tc-last

    QED : te ∙∈ (_m ∷ s .history)
    QED with ⟫ te∈
    ... | ⟫ there te∈ = te∈-monotonic $ IH te∈
    ... | ⟫ here (∈-Timeout-TE ∈-TE) = -, here refl
    ... | ⟫ here (∈-Timeout-TC te∈tc) = te∈-monotonic QED′
      where
      QED′ : te ∙∈ s .history
      QED′ = let tc , tc≡ = destruct-Is-just $ Any⇒Is-just te∈tc
             in  telast∈ᴹ⇒te∈ Rs te≡ tc≡ (Any-just tc≡ te∈tc)
  ... | TimerExpired _ _ = QED
    where
    QED : te ∙∈ (_ ∷ s .history)
    QED with ⟫ te∈
    ... | ⟫ there te∈ = te∈-monotonic $ IH te∈
    ... | ⟫ here (∈-Timeout-TE ∈-TE) = -, here refl
    ... | ⟫ here (∈-Timeout-TC te∈tc) = te∈-monotonic QED′
      where
      QED′ : te ∙∈ s .history
      QED′ = let tc , tc≡ = destruct-Is-just $ Any⇒Is-just te∈tc
             in  telast∈ᴹ⇒te∈ Rs te≡ tc≡ (Any-just tc≡ te∈tc)
  ... | AdvanceRoundQC _ _ _ = IH te∈
  ... | AdvanceRoundTC _ _ _ = IH te∈
  ... | AdvanceRoundNoOp _ _ _ = IH te∈
  ... | Lock _ _ = IH te∈
  ... | Commit _ _ = IH te∈
  ... | CommitNoOp _ _ = IH te∈
  ... | VoteBlock {b = b} _ _ _ = te∈-monotonic QED
    where
    QED : te ∙∈ s .history
    QED with ⟫ there te∈ ← ⟫ te∈ = IH te∈
  ... | VoteBlockNoOp _ _ = IH te∈
  ... | RegisterProposal _ _ _ _ _ = IH te∈
  ... | RegisterTimeout _ _ _ _ = IH te∈
  ... | RegisterTC _ _ _ _ = IH te∈
  ... | RegisterVote _ _ _ _ _ _ = IH te∈


MessageTimeout⇒StepTimeout : ∀ {te r} ⦃ _ : Honest p ⦄ →
    (st : p ⦂ s .currentTime ⊢ ls — menv —→ ls′) →
  ∙ (∃ λ mtc → just [ r ?∣ Timeout (te , mtc) ⟩ ≡ menv)
    ─────────────────────────────────────────────────────
    StepTimeout p te (_ ⊢ st)
MessageTimeout⇒StepTimeout (EnoughTimeouts _ _ _ _) (_ , refl) = refl , refl
MessageTimeout⇒StepTimeout (TimerExpired _ _) (_ , refl) = refl , refl

-- ** Inverse MessageTimeout⇒StepTimeout, not needed yet.
{-
StepTimeout⇒MessageTimeout : ∀ {te}
    (st : p ⦂ s .currentTime ⊢ ls — menv —→ ls′) →
  ∙ StepTimeout p te (_ ⊢ st)
    ─────────────────────────────────────────────────────
    ∃ λ mtc → just [ Timeout (te , mtc) ⟩ ≡ menv
-}

TimeoutMsg⇒TimeoutStep : ∀ {s} (Rs : Reachable s) ⦃ _ : Honest p ⦄ →
  ∙ te .node ≡ p
  ∙ te ∙∈ s .history
    ───────────────────────────────
    Rs ∋⋯ StepTimeout p te
TimeoutMsg⇒TimeoutStep (_ , refl , (_ ∎)) te≡ (_ , ())
TimeoutMsg⇒TimeoutStep (_ , init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) te≡ tm∈ =
  TimeoutMsg⇒TimeoutStep (_ , init , tr) te≡ tm∈
TimeoutMsg⇒TimeoutStep (_ , init , (_ ⟨ Deliver _ ⟩←— tr)) te≡ tm∈ =
  TimeoutMsg⇒TimeoutStep (_ , init , tr) te≡ tm∈
TimeoutMsg⇒TimeoutStep {p = p} {te = te}
  (_ , init , (_ ⟨ DishonestLocalStep {env = env} {p = p′} ¬hp′ ¬frg ∣ s ⟩←— tr))
  ⦃ hp ⦄ te≡ tm∈
  = TimeoutMsg⇒TimeoutStep (_ , init , tr) te≡ ≪tm∈
  where
  ≪tm∈ : te ∙∈ s .history
  ≪tm∈ with ⟫ tm∈
  ... | ⟫ _ , there tm∈ = -, tm∈
  ... | ⟫ mtc , here refl = QED
    where
    M = Timeout (te , mtc)

    te∈m : te -∈ᴹ- M
    te∈m = ∈-Timeout-TE ∈-TE

    te∈ : Any (te -∈ᴹ-_) (s .history)
    te∈ = ¬frg te te∈m (subst Honest (sym te≡) hp)

    QED : te ∙∈ s .history
    QED = te∈ᴹ⇒te∈ (_ , init , tr) te≡ te∈
TimeoutMsg⇒TimeoutStep {p = p}{te = te}
  (_ , init , (s′ ⟨ LocalStep {p = p′} {menv = menv}{ls′} st ∣ s ⟩←— tr))
  ⦃ hp ⦄ te≡ (mtc , tm∈)
  with IH ← TimeoutMsg⇒TimeoutStep {p = p}{te = te} (_ , init , tr) te≡
  with p ≟ p′
... | no p≢ = there $ IH m∈history
  where
  m∈history : te ∙∈ s .history
  m∈history with ⟫ menv
  ... | ⟫ nothing  = -, tm∈
  ... | ⟫ just env = -, flip L.Any.tail tm∈ (λ where
    refl → p≢ $ trans (sym te≡)
                      (M.All.drop-just $ M.All.drop-just $ ownMessage {s = s} st))
... | yes refl
    with StepTimeout? p te ((_ ⊢ st) ⦃ hp ⦄)
... | yes stT = here stT
... | no ¬stT with menv
... | nothing  = there $ IH (-, tm∈)
... | just env = there $ IH $ -, L.Any.tail (λ where
  refl → ¬stT $ MessageTimeout⇒StepTimeout {s = s} ⦃ hp ⦄ st (-, refl)) tm∈

mutual
  tclast∈m⇒te∈ : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
    ∙ te .node ≡ p
    ∙ te ∈ tc .tes
    ∙ (s ＠ p′) .tc-last ≡ just tc
      ───────────────────────────
      te ∙∈ s .history
  tclast∈m⇒te∈ {tc = tc} {s = s} Rs te≡ te∈ tc≡ =
    tc∈⇒te∈ Rs te≡ te∈ tc∈
    where
    tc∈ : tc ∙∈ s .history
    tc∈ = M.All.drop-just $ subst (All _) tc≡ $ tc-last∈history Rs

  tc∈m⇒te∈ : ∀ {s} → Reachable s → ⦃ Honest p ⦄ →
    ∙ te .node ≡ p
    ∙ te ∈ tc .tes
    ∙ Any (tc tc∈-Message_) (s .history)
      ──────────────────────────────────
      te ∙∈ s .history
  tc∈m⇒te∈ {p}{te}{tc} (_ , refl , (_ ∎)) _ _ ()
  tc∈m⇒te∈ {p}{te}{tc} (_ , s-init , (_ ⟨ st ∣ s ⟩←— tr)) ⦃ hp ⦄ te≡@refl te∈ tc∈
    with Rs ← _ , s-init , tr
    with IH ← tc∈m⇒te∈ {p}{te}{tc} Rs te≡ te∈
    with IHₗ ← (λ {p′} ⦃ _ : Honest p′ ⦄ → tclast∈m⇒te∈ {p}{p′}{te}{tc} Rs te≡ te∈)
    with st
  ... | WaitUntil _ _ _ = IH tc∈
  ... | Deliver _ = IH tc∈
  ... | DishonestLocalStep {env = env} {p = p′} ¬hp′ ¬frg
    = te∈-monotonic QED
    where
    QED : te ∙∈ s .history
    QED with ⟫ tc∈
    ... | ⟫ there tc∈ = IH tc∈
    ... | ⟫ here tc∈M = te∈ᴹ⇒te∈ Rs te≡ $ ¬frg te (tc∈⇒te∈ᴹ tc∈M) hp
      where
      te∈tc : te -∈-TC- tc
      te∈tc = ∈-TC (L.Any.map (λ where refl → ∈-TE) te∈)

      tc∈⇒te∈ᴹ : tc tc∈-Message_ ⊆¹ te -∈ᴹ-_
      tc∈⇒te∈ᴹ = λ where
        (tc∈-Propose refl) → ∈-Propose-TC (just te∈tc)
        tc∈-TCFormed       → ∈-TCFormed te∈tc
        (tc∈-Timeout refl) → ∈-Timeout-TC (just te∈tc)
  ... | LocalStep {p = p} {ls′ = ls′} st
    with st
  ... | InitTC _ tc≡ = te∈-monotonic QED
    where
    QED : te ∙∈ s .history
    QED with ⟫ tc∈
    ... | ⟫ here tc∈-TCFormed = IHₗ tc≡
    ... | ⟫ there tc∈         = IH tc∈
  ... | InitNoTC _ _ = IH tc∈
  ... | ProposeBlock {txn = txn} _ _ = te∈-monotonic $ case tc∈ of λ where
    (here (tc∈-Propose tc≡)) → IHₗ tc≡
    (there tc∈)              → IH tc∈
  ... | ProposeBlockNoOp _ _ = IH tc∈
  ... | EnoughTimeouts _ _ _ _ = te∈-monotonic $ case tc∈ of λ where
    (here (tc∈-Timeout tc≡)) → IHₗ tc≡
    (there tc∈)              → IH tc∈
  ... | TimerExpired _ _ = te∈-monotonic $ case tc∈ of λ where
    (here (tc∈-Timeout tc≡)) → IHₗ tc≡
    (there tc∈)              → IH tc∈
  ... | AdvanceRoundQC _ _ _ = IH tc∈
  ... | AdvanceRoundTC _ _ _ = IH tc∈
  ... | AdvanceRoundNoOp _ _ _ = IH tc∈
  ... | Lock _ _ = IH tc∈
  ... | Commit _ _ = IH tc∈
  ... | CommitNoOp _ _ = IH tc∈
  ... | VoteBlock {b = b} _ _ _ with ⟫ there tc∈ ← ⟫ tc∈ = te∈-monotonic $ IH tc∈
  ... | VoteBlockNoOp _ _ = IH tc∈
  ... | RegisterProposal _ _ _ _ _ = IH tc∈
  ... | RegisterTimeout _ _ _ _ = IH tc∈
  ... | RegisterTC _ _ _ _ = IH tc∈
  ... | RegisterVote _ _ _ _ _ _ = IH tc∈

  tc∈⇒te∈ : ∀ {s} → Reachable s → ⦃ Honest p ⦄ →
    ∙ te .node ≡ p
    ∙ te ∈ tc .tes
    ∙ tc ∙∈ s .history
      ────────────────
      te ∙∈ s .history
  tc∈⇒te∈ Rs te≡ te∈ = λ where
    (formedTC ftc)   → L.All.lookup ftc te∈
    (receivedTC tc∈) → tc∈m⇒te∈ Rs te≡ te∈ tc∈

te∈tc⇒Timeout : ∀ {s} (Rs : Reachable s) ⦃ _ : Honest p ⦄ →
  ∙ tc ∙∈ s .history
  ∙ te .node ≡ p
  ∙ te ∈ tc .tes
    ──────────────────────
    Rs ∋⋯ StepTimeout p te
te∈tc⇒Timeout Rs tc∈ te≡ te∈ =
  TimeoutMsg⇒TimeoutStep Rs te≡ $ tc∈⇒te∈ Rs te≡ te∈ tc∈

sameRound-lemma : ∀ {s s′} →  ⦃ _ : Honest p ⦄ → ⦃ _ : Honest p′ ⦄ → Reachable s →
    let ls  = s ＠ p
        ls′ = s′ ＠ p
    in
    ∙ 1 + ls .r-cur ≡ ls .r-vote
    ∙ s′ ↞— s
    ∙ ls .r-cur ≡ ls′ .r-cur
      ────────────────────────────
      1 + ls′ .r-cur ≡ ls′ .r-vote
sameRound-lemma Rs 1+r-cur≡r-vote (_ ∎) _ = 1+r-cur≡r-vote
sameRound-lemma {p = p}{s = s₀} ⦃ hp ⦄ ⦃ hp′ ⦄ Rs₀ 1+r-cur≡r-vote (_ ⟨ st ∣ s ⟩←— tr) ls≡
  with IH ← sameRound-lemma {s′ = s} ⦃ hp ⦄ ⦃ hp′ ⦄ Rs₀ 1+r-cur≡r-vote tr
  with st
... | WaitUntil _ _ _
  = IH ls≡
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p}{s .stateMap} (honestTPMessage tpm)
  = IH ls≡
... | DishonestLocalStep _ _ = IH ls≡
... | LocalStep {p = p′}{ls′ = ls′} st
  with lookup✓ ← pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with lookup✖ ← (λ p≢ → pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap))
  with p ≟ p′
... | no p≢ rewrite lookup✖ p≢ | sym (lookup✖ p≢) = IH ls≡
... | yes refl
  with st
... | InitTC _ _ rewrite lookup✓ = IH ls≡
... | InitNoTC _ _ rewrite lookup✓ = IH ls≡
... | ProposeBlockNoOp _ _ rewrite lookup✓ = IH ls≡
... | RegisterProposal _ _ _ _ _ rewrite lookup✓ = IH ls≡
... | EnoughTimeouts _ _ _ _ rewrite lookup✓ = refl
... | RegisterTimeout _ _ _ _ rewrite lookup✓ = IH ls≡
... | RegisterTC _ _ _ _ rewrite lookup✓ = IH ls≡
... | TimerExpired _ _ rewrite lookup✓ = refl
... | RegisterVote _ _ _ _ _ _ rewrite lookup✓ = IH ls≡
... | AdvanceRoundQC _ _ qc> rewrite lookup✓
  = ⊥-elim (Nat.<⇒≢ ls′> ls≡)
  where
    open Nat.≤-Reasoning renaming (_∎ to _■)

    ls₀ = s₀ ＠ʰ hp
    _ls = s ＠ʰ hp

    ls′> : ls′ .r-cur > ls₀ .r-cur
    ls′> = begin-strict
        ls₀ .r-cur
      ≤⟨ r-cur-mono {s′ = s}{s₀} ⦃ hp ⦄ tr ⟩
        _ls .r-cur
      <⟨ Nat.s≤s qc> ⟩
        ls′ .r-cur
      ■
... | AdvanceRoundTC _ _ tc≥ rewrite lookup✓
  = ⊥-elim (Nat.<⇒≢ ls′> ls≡)
  where
  open Nat.≤-Reasoning renaming (_∎ to _■)

  ls₀ = s₀ ＠ʰ hp
  _ls = s ＠ʰ hp

  ls′> : ls′ .r-cur > ls₀ .r-cur
  ls′> = begin-strict
      ls₀ .r-cur
    ≤⟨ r-cur-mono {s′ = s}{s₀} ⦃ hp ⦄ tr ⟩
      _ls .r-cur
    <⟨ Nat.s≤s tc≥ ⟩
      ls′ .r-cur
    ■
... | AdvanceRoundNoOp _ _ _ rewrite lookup✓ = IH ls≡
... | Lock _ (isHighest qc∈ _) rewrite lookup✓ = IH ls≡
... | CommitNoOp _ _ rewrite lookup✓ = IH ls≡
... | VoteBlockNoOp _ _ rewrite lookup✓ = IH ls≡
... | Commit _ _ rewrite lookup✓ = IH ls≡
... | ProposeBlock _ _ rewrite lookup✓ = IH ls≡
... | VoteBlock _ _ (refl , r> , _) rewrite lookup✓
  with ih ← IH ls≡
       = let r = (s ＠ʰ hp) .r-cur in
       ⊥-elim $ Nat.<⇒≯ r> $ subst (1 + r ≤_) ih (Nat.n<1+n r)

timedOut?⇒r-cur-vote : ∀ {s s′ te} → ⦃ _ : Honest p ⦄ → Reachable s → let ls′ = s′ ＠ p in
  ∙ StepTimeout p te ◃ s
  ∙ s′ ↞— s
  ∙ te ∙round ≡ ls′ .r-cur
    ────────────────────────────
    1 + ls′ .r-cur ≡ ls′ .r-vote
timedOut?⇒r-cur-vote {p = p} {s = s} {s′}{te} ⦃ hp ⦄ Rs
  st-timeout@(st , ⟪s , refl , refl , refl , tst-timeout) tr r≡
  = sameRound-lemma {p = p} {s = s} ⦃ hp ⦄ ⦃ hp ⦄ Rs r-cur-vote tr ≪r≡
  where
  tst = st .theStep

  ls₁  = s ＠ p
  _ls′ = s′ ＠ p

  r-cur-vote : 1 + ls₁ .r-cur ≡ ls₁ .r-vote
  r-cur-vote
     with ⟫ tst | ⟫ tst-timeout
  ... | ⟫ EnoughTimeouts ph≡ _ _ _ | ⟫ refl , _
    rewrite pLookup∘updateAt p ⦃ hp ⦄ {const $ recordTimeout (⟪s ＠ʰ hp)} (⟪s .stateMap)
    = refl
  ... | ⟫ TimerExpired   ph≡ _     | ⟫ refl , _
    rewrite pLookup∘updateAt p ⦃ hp ⦄ {const $ recordTimeout (⟪s ＠ʰ hp)} (⟪s .stateMap)
    = refl

  r-cur-te : ls₁ .r-cur ≡ te ∙round
  r-cur-te
    with ⟫ tst | ⟫ tst-timeout
  ... | ⟫ EnoughTimeouts ph≡ _ _ _ | ⟫ refl , refl
    rewrite pLookup∘updateAt p  ⦃ hp ⦄ {const $ recordTimeout (⟪s ＠ʰ hp)} (⟪s .stateMap)
    = refl
  ... | ⟫ TimerExpired   ph≡ _     | ⟫ refl , refl
    rewrite pLookup∘updateAt p  ⦃ hp ⦄ {const $ recordTimeout (⟪s ＠ʰ hp)} (⟪s .stateMap)
    = refl

  ≪r≡ : ls₁ .r-cur ≡ _ls′ .r-cur
  ≪r≡ = trans r-cur-te r≡
