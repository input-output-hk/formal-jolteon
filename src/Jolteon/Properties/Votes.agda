{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Votes (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Global.NoForging ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.State.Invariants ⋯
open import Jolteon.Properties.State.TC ⋯

open import Jolteon.Properties.Votes.Core ⋯ public
open import Jolteon.Properties.Votes.NotGenesis ⋯ public

mutual
  qchigh∈ᴹ⇒vs∈ : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
    ∙ vs ∙pid ≡ p
    ∙ ¬Genesis vs
    ∙ qc ≡ (s ＠ p′) .qc-high
    ∙ vs -∈-QC- qc
      ──────────────────────
      vs ∙∈ s .history
  qchigh∈ᴹ⇒vs∈ {p}{p′}{vs}{qc}{s} Rs vs≡ vs≢ qc≡ (∈-QC p∈)
    = qchigh⇒vs∈ Rs vs≡ (λ where refl → vs≢ refl) vs∈ qc≡
    where
    vs∈ : vs ∈ qcVoteShares qc
    vs∈ = L.Mem.∈-map⁺ (qc .payload signed-by_) p∈

  tclast∈ᴹ⇒vs∈ : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ ⦃ _ : Honest p′ ⦄ →
    ∙ vs ∙pid ≡ p
    ∙ ¬Genesis vs
    ∙ (s ＠ p′) .tc-last ≡ just tc
    ∙ (BR ∶ vs -∈-TC- tc)
      ───────────────────────────
      vs ∙∈ s .history
  tclast∈ᴹ⇒vs∈ {p}{p′}{vs}{tc}{s} Rs vs≡ vs≢ tc≡ (∈-TC vs∈)
    with te , te∈ , ∈-QC p∈ ← satisfied′ $ L.Any.map (λ where (∈-TE-QC vs∈qcTE) → vs∈qcTE) vs∈
    = qc∈⇒vs∈ {qc = te ∙qcTE} Rs vs≡ vs≢
        (L.Mem.∈-map⁺ ((te ∙qcTE) .payload signed-by_) p∈)
        (qc-tc-last Rs $ subst (Any _) (sym tc≡) $ just (qcTE-lemma {tc = tc} te∈))

  vs∈ᴹ⇒vs∈ : ∀ {s} → Reachable s → ⦃ Honest p ⦄ →
    ∙ vs ∙pid ≡ p
    ∙ ¬Genesis vs
    ∙ Any (BR ∶ vs -∈ᴹ-_) (s .history)
      ────────────────────────────────
      vs ∙∈ s .history
  vs∈ᴹ⇒vs∈ (_ , refl , (_ ∎)) _ _ ()
  vs∈ᴹ⇒vs∈ {p}{vs} (_ , s-init , (_ ⟨ st ∣ s ⟩←— tr)) ⦃ hp ⦄ vs≡ vs≢ vs∈
    with Rs ← _ , s-init , tr
    with IH ← vs∈ᴹ⇒vs∈ {p}{vs} Rs vs≡ vs≢
    with IHₕ ← (λ {p′} ⦃ _ : Honest p′ ⦄ {qc} → qchigh∈ᴹ⇒vs∈ {p}{p′}{vs}{qc} Rs vs≡ vs≢)
    with IHₗ ← (λ {p′} ⦃ _ : Honest p′ ⦄ {tc} → tclast∈ᴹ⇒vs∈ {p}{p′}{vs}{tc} Rs vs≡ vs≢)
    with st
  ... | WaitUntil _ _ _ = IH vs∈
  ... | Deliver _ = IH vs∈
  ... | DishonestLocalStep {env = env} {p = p′} ¬hp′ ¬frg
    = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ vs∈
    ... | ⟫ there vs∈ = IH vs∈
    ... | ⟫ here vs∈M = IH $ ¬frg vs vs∈M (subst Honest (sym vs≡) hp)
  ... | LocalStep {p = p} {ls′ = ls′} st
    with st
  ... | InitTC {tc = tc} _ tc≡ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ vs∈
    ... | ⟫ there vs∈ = IH vs∈
    ... | ⟫ here (∈-TCFormed vs∈tc) = IHₗ tc≡ vs∈tc
  ... | InitNoTC _ _ = IH vs∈
  ... | ProposeBlock {txn = txn} _ _ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ vs∈
    ... | ⟫ there vs∈ = IH vs∈
    ... | ⟫ here (∈-Propose-QC vs∈qc) = IHₕ refl vs∈qc
    ... | ⟫ here (∈-Propose-TC vs∈tc) = uncurry IHₗ $ destruct-Any-just vs∈tc .proj₂
  ... | ProposeBlockNoOp _ _ = IH vs∈
  ... | EnoughTimeouts _ _ _ _ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ vs∈
    ... | ⟫ there vs∈ = IH vs∈
    ... | ⟫ here (∈-Timeout-TE (∈-TE-QC vs∈teQC)) = IHₕ refl vs∈teQC
    ... | ⟫ here (∈-Timeout-TC vs∈tc) = uncurry IHₗ $ destruct-Any-just vs∈tc .proj₂
  ... | TimerExpired _ _ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ vs∈
    ... | ⟫ there vs∈ = IH vs∈
    ... | ⟫ here (∈-Timeout-TE (∈-TE-QC vs∈teQC)) = IHₕ refl vs∈teQC
    ... | ⟫ here (∈-Timeout-TC vs∈tc) = uncurry IHₗ $ destruct-Any-just vs∈tc .proj₂
  ... | AdvanceRoundQC _ _ _ = IH vs∈
  ... | AdvanceRoundTC _ _ _ = IH vs∈
  ... | AdvanceRoundNoOp _ _ _ = IH vs∈
  ... | Lock _ _ = IH vs∈
  ... | Commit _ _ = IH vs∈
  ... | CommitNoOp _ _ = IH vs∈
  ... | VoteBlock {b = b} _ _ _ = QED
    where
    QED : vs ∙∈ (_ ∷ s .history)
    QED with ⟫ vs∈
    ... | ⟫ there vs∈ = there $ IH vs∈
    ... | ⟫ here ∈-Vote = here refl
  ... | VoteBlockNoOp _ _ = IH vs∈
  ... | RegisterProposal _ _ _ _ _ = IH vs∈
  ... | RegisterTimeout _ _ _ _ = IH vs∈
  ... | RegisterTC _ _ _ _ = IH vs∈
  ... | RegisterVote _ _ _ _ _ _ = IH vs∈

  qchigh⇒vs∈ : ∀ {s} → Reachable s → ⦃ Honest p ⦄ → ⦃ _ : Honest p′ ⦄ →
    ∙ vs ∙pid ≡ p
    ∙ ¬Genesis qc
    ∙ vs ∈ qcVoteShares qc
    ∙ qc ≡ (s ＠ p′) .qc-high
      ──────────────────────
      vs ∙∈ s .history
  qchigh⇒vs∈ Rs vs≡ qc≢ vs∈ refl
    = qc∈⇒vs∈ Rs vs≡ qc≢ vs∈
    $ qc-db⊆history Rs
    $ qc-high∈db Rs

  qc∈m⇒vs∈ : ∀ {s} → Reachable s → ⦃ _ : Honest p ⦄ → let ms = s .history in
    ∙ vs ∙pid ≡ p
    ∙ ¬Genesis qc
    ∙ vs ∈ qcVoteShares qc
    ∙ Any (qc qc∈-Message_) ms
      ────────────────────────
      vs ∙∈ ms
  qc∈m⇒vs∈ (_ , refl , (_ ∎)) _ _ _ ()
  qc∈m⇒vs∈ {p}{vs}{qc} (_ , s-init , (_ ⟨ st ∣ s ⟩←— tr)) ⦃ hp ⦄ vs≡ qc≢ vs∈ qc∈
    with Rs ← _ , s-init , tr
    with IH₀ ← qc∈⇒vs∈ {qc = qc} Rs vs≡ qc≢ vs∈
    with IH ← qc∈m⇒vs∈ {p}{vs}{qc} Rs vs≡ qc≢ vs∈
    with IHₕ ← (λ {p} ⦃ _ : Honest p ⦄ → qchigh⇒vs∈ {qc = qc} Rs vs≡ qc≢ vs∈)
    with st
  ... | WaitUntil _ _ _ = IH qc∈
  ... | Deliver _ = IH qc∈
  ... | DishonestLocalStep {env = env} {p = p′} ¬hp′ ¬frg
    = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ qc∈
    ... | ⟫ there qc∈ = IH qc∈
    ... | ⟫ here qc∈M = vs∈ᴹ⇒vs∈ Rs vs≡ vs≢ $ ¬frg vs (qc∈⇒vs∈ᴹ qc∈M) (subst Honest (sym vs≡) hp)
      where
      vs≢ : ¬Genesis vs
      vs≢ = subst (_≢ _) (cong proj₁ $ L.All.lookup (qcVoteShares-All qc) vs∈) qc≢

      vs∈qc : vs -∈-QC- qc
      vs∈qc with L.Mem.∈-map⁻ (qc .payload signed-by_) vs∈
      ... | p , p∈ , refl
        = ∈-QC p∈

      vs∈tc : ∀ {tc} → qc ∈₁ qcs⁺ tc → BR ∶ vs -∈-TC- tc
      vs∈tc {tc} qc∈ = ∈-TC qc∈tes
        where
        qc∈qcsTE : qc ∈ qcsTES (tc .tes)
        qc∈qcsTE = subst (qc ∈_) (qcs≡qcsTES tc) qc∈

        qc∈tes : Any (vs -∈-TE-_) (tc .tes)
        qc∈tes with _ , qc∈tes , refl ← L.Mem.∈-map⁻ _∙qcTE qc∈qcsTE
          = L.Any.map (λ where refl → ∈-TE-QC vs∈qc) qc∈tes

      qc∈⇒vs∈ᴹ : qc qc∈-Message_ ⊆¹ BR ∶ vs -∈ᴹ-_
      qc∈⇒vs∈ᴹ = λ where
        (qc∈-Propose refl) → ∈-Propose-QC vs∈qc
        (qc∈-ProposeTC refl qc∈) → ∈-Propose-TC (just (vs∈tc qc∈))
        (qc∈-TCFormed qc∈) → ∈-TCFormed (vs∈tc qc∈)
        (qc∈-Timeout refl) → ∈-Timeout-TE (∈-TE-QC vs∈qc)
        (qc∈-TimeoutTC refl qc∈) → ∈-Timeout-TC (just (vs∈tc qc∈))
  ... | LocalStep {p = p} {ls′ = ls′} st
    with st
  ... | InitTC {tc = tc} _ tc≡ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ qc∈
    ... | ⟫ here (qc∈-TCFormed qc∈)
        = qc∈⇒vs∈ Rs vs≡ qc≢ vs∈
        $ L.All.lookup (tc-last⇒qc∈ Rs tc≡) qc∈
    ... | ⟫ there qc∈
        = IH qc∈
  ... | InitNoTC _ _ = IH qc∈
  ... | ProposeBlock {txn = txn} _ _ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ qc∈
    ... | ⟫ here (qc∈-Propose qc≡) = IHₕ qc≡
    ... | ⟫ here (qc∈-ProposeTC tc≡ qc∈) = IH₀ $ L.All.lookup (tc-last⇒qc∈ Rs tc≡) qc∈
    ... | ⟫ there qc∈ = IH qc∈
  ... | ProposeBlockNoOp _ _ = IH qc∈
  ... | EnoughTimeouts _ _ _ _ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ qc∈
    ... | ⟫ here (qc∈-Timeout qc≡) = IHₕ qc≡
    ... | ⟫ here (qc∈-TimeoutTC tc≡ qc∈) = IH₀ $ L.All.lookup (tc-last⇒qc∈ Rs tc≡) qc∈
    ... | ⟫ there qc∈ = IH qc∈
  ... | TimerExpired _ _ = there QED
    where
    QED : vs ∙∈ s .history
    QED with ⟫ qc∈
    ... | ⟫ here (qc∈-Timeout qc≡) = IHₕ qc≡
    ... | ⟫ here (qc∈-TimeoutTC tc≡ qc∈) = IH₀ $ L.All.lookup (tc-last⇒qc∈ Rs tc≡) qc∈
    ... | ⟫ there qc∈ = IH qc∈
  ... | AdvanceRoundQC _ _ _ = IH qc∈
  ... | AdvanceRoundTC _ _ _ = IH qc∈
  ... | AdvanceRoundNoOp _ _ _ = IH qc∈
  ... | Lock _ _ = IH qc∈
  ... | Commit _ _ = IH qc∈
  ... | CommitNoOp _ _ = IH qc∈
  ... | VoteBlock {b = b} _ _ _
    with ⟫ there qc∈ ← ⟫ qc∈
    = there $ IH qc∈
  ... | VoteBlockNoOp _ _ = IH qc∈
  ... | RegisterProposal _ _ _ _ _ = IH qc∈
  ... | RegisterTimeout _ _ _ _ = IH qc∈
  ... | RegisterTC _ _ _ _ = IH qc∈
  ... | RegisterVote _ _ _ _ _ _ = IH qc∈

  qc∈⇒vs∈ : ∀ {s} → Reachable s → ⦃ Honest p ⦄ → let ms = s .history in
    ∙ vs ∙pid ≡ p
    ∙ ¬Genesis qc
    ∙ vs ∈ qcVoteShares qc
    ∙ qc ∙∈ ms
      ────────────────────
      vs ∙∈ ms
  qc∈⇒vs∈ Rs vs≡ qc≢ vs∈ = λ where
    (initialQC qc≡)   → ⊥-elim $ qc≢ (cong _∙blockId qc≡)
    (formedQC fqc)    → L.All.lookup fqc vs∈
    (receivedQC qc∈m) → qc∈m⇒vs∈ Rs vs≡ qc≢ vs∈ qc∈m

qc⇒Vote : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → (let ms = s .history) →
  ∙ ¬Genesis qc
  ∙ qc ∙∈ ms
  ∙ p ∈ qc .shares
    ───────────────────────────────
    (qc .payload signed-by p) ∙∈ ms
qc⇒Vote {p}{qc}{s = s} Rs qc≢ qc∈ p∈ =
  qc∈⇒vs∈ Rs refl qc≢ (L.Mem.∈-map⁺ (qc .payload signed-by_) p∈) qc∈

Vote∈votes' : ∀ {ms} →
  ∙ vs ∙blockId ≡ b ∙blockId
  ∙ p ≡ vs ∙pid
  ∙ vs ∙∈ ms
    ────────────────────────
    p ∈ votes' b ms
Vote∈votes' {vs = vs} {b = b} refl refl (here refl) with vs ∙blockId ≟ b ∙blockId
... | no ¬id≡ = ⊥-elim (¬id≡ refl)
... | yes refl = here refl
Vote∈votes' {b = b} {ms = m ∷ _} id≡ p≡ (there v∈) with getVoteFor b m
... | just _  = there (Vote∈votes' id≡ p≡ v∈)
... | nothing = Vote∈votes' id≡ p≡ v∈

Vote∈votes : ∀ {ms} →
  ∙ vs ∙blockId ≡ b ∙blockId
  ∙ p ≡ vs ∙pid
  ∙ vs ∙∈ ms
    ────────────────────────────
    p ∈ votes b ms
Vote∈votes id≡ p≡ v∈ = nub-⊆⁺ $ Vote∈votes' id≡ p≡ v∈

qc⇒vote : ∀ {s} ⦃ _ : Honest p ⦄ → Reachable s → let ms = s .history in
  ∙ qc ∙∈ ms
  ∙ p ∈ qc .shares
  ∙ b -certified-by- qc
    ───────────────────
    p ∈ votes b ms
qc⇒vote {qc = qc} ⦃ hp ⦄ Rs qc∈ p∈ cb@(refl , refl) =
  Vote∈votes refl refl $ qc⇒Vote Rs (¬certified-by-genesis {qc = qc} cb) qc∈ p∈

{- ** NOT TRUE
GCB⇒Majority : ∀ {s} → Reachable s →
  GloballyCertifiedBlockIn s b
  ────────────────────────────
  MajorityVotes b s
-}

GCB⇒MoreThanF : ∀ {s} → Reachable s →
  GloballyCertifiedBlockIn s b
  ────────────────────────────
  MoreThanF-Honest b s
GCB⇒MoreThanF {b}{s} Rs (qc , cb@(refl , refl) , qc∈)
  rewrite honestVotes≡ b (s .history)
  = QED
  where

  _ms = s .history
  sh = qc .shares
  hsh = filter honest? sh
  hvs = filter honest? $ votes b _ms

  mtfh : MoreThanF hsh
  mtfh = Majority⇒MoreThanF sh (getUnique qc) (getQuorum qc)

  uh : Unique hsh
  uh = L.AP.filter⁺ honest? (getUnique qc)

  allh : ∀ {p} → p ∈ hsh → Honest p
  allh = L.All.lookup (L.All.all-filter honest? sh)

  p∈⇒ : ∀ {p} → p ∈ hsh → p ∈ sh
  p∈⇒ = proj₁ ∘ L.Mem.∈-filter⁻ honest?

  QED : MoreThanF hvs
  QED = moreThanF-mono uh (λ {p} p∈ →
     L.Mem.∈-filter⁺ honest? (qc⇒vote ⦃ allh p∈ ⦄ Rs qc∈ (p∈⇒ p∈) cb) (allh p∈)) mtfh

honest∈votes⇒StepVotes : ∀ {s} (Rs : Reachable s) → let ms = s .history in
  ∙ Honest p
  ∙ p ∈ votes b ms
    ───────────────────
    Rs ∋⋯ StepVotes p b
honest∈votes⇒StepVotes (_ , refl , (_ ∎)) _ ()
honest∈votes⇒StepVotes (_ , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) hp p∈
  = honest∈votes⇒StepVotes (_ , s-init , tr) hp p∈
honest∈votes⇒StepVotes (_ , s-init , (_ ⟨ Deliver _ ⟩←— tr)) hp p∈
  = honest∈votes⇒StepVotes (_ , s-init , tr) hp p∈
honest∈votes⇒StepVotes  {p}{b}
  Rs₀@(_ , s-init , (_ ⟨ DishonestLocalStep {env = env} {p = p′} ¬hp′ ¬frg ∣ s ⟩←— tr))
  hp p∈
  = honest∈votes⇒StepVotes (_ , s-init , tr) hp p∈′
  where
  b≢ : ¬Genesis b
  b≢ = honest∈votes⇒¬Genesis Rs₀ hp p∈

  p∈′ : p ∈ votes b (s .history)
  p∈′
    -- p∈ : p ∈ votes b (env .content ∷ s .history)
    with env .content
  ... | Propose  _ = p∈
  ... | TCFormed _ = p∈
  ... | Timeout _  = p∈
  ... | Vote vs
    -- p∈ : p ∈ votes b (Vote vs ∷ s .history)
    with vs ∙blockId ≟ b ∙blockId
    -- p∈ : p ∈ votes b (s .history)
  ... | no  _ = p∈
    -- p∈ : p ∈ nub (vs ∙pid ∷ votes' b (s .history))
  ... | yes vs≡
    with vs ∙pid ∈? votes' b (s .history)
    -- p∈ : p ∈ votes b (s .history)
  ... | yes _ = p∈
    -- p∈ : p ∈ vs ∙pid ∷ votes b (s .history)
  ... | no _
    with ⟫ p∈
  ... | ⟫ there p∈ = p∈
  ... | ⟫ here refl
    = QED
    where
    p∈ᴹ : Any (vs -∈ᴹ-_) (s .history)
    p∈ᴹ = ¬frg vs ∈-Vote hp

    vs∈ : vs ∙∈ s .history
    vs∈ = vs∈ᴹ⇒vs∈ (_ , s-init , tr) ⦃ hp ⦄ refl (subst (_≢ genesisId) (sym vs≡) b≢) p∈ᴹ

    QED : p ∈ votes b (s .history)
    QED = nub-⊆⁺ (∈-mapMaybe⁺ (getVoteFor b) vs∈ get≡)
      where
      get≡ : getVoteFor b (Vote vs) ≡ just p
      get≡ rewrite dec-yes ((vs ∙blockId) ≟ (b ∙blockId)) vs≡ .proj₂ = refl
honest∈votes⇒StepVotes {p}{b}
  (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {menv = menv} {ls′ = ls′} st ∣ s ⟩←— tr))
  hp p∈
  with IH ← honest∈votes⇒StepVotes {p}{b} (_ , s-init , tr) hp
  with st
... | InitTC _ _ = there $ IH p∈
... | InitNoTC _ _ = there $ IH p∈
... | ProposeBlockNoOp _ _ = there $ IH p∈
... | RegisterProposal _ _ _ _ _ = there $ IH p∈
... | EnoughTimeouts _ _ _ _ = there $ IH p∈
... | RegisterTimeout _ _ _ _ = there $ IH p∈
... | RegisterTC _ _ _ _ = there $ IH p∈
... | TimerExpired _ _ = there $ IH p∈
... | RegisterVote _ _ _ _ _ _ = there $ IH p∈
... | AdvanceRoundQC _ _ _ = there $ IH p∈
... | AdvanceRoundTC _ _ _ = there $ IH p∈
... | AdvanceRoundNoOp _ _ _ = there $ IH p∈
... | Lock _ _ = there $ IH p∈
... | CommitNoOp _ _ = there $ IH p∈
... | VoteBlockNoOp _ _ = there $ IH p∈
... | Commit _ _ = there $ IH p∈
... | ProposeBlock _ _ = there $ IH p∈
... | VoteBlock {b = b′} _ _ _
  with b′ ∙blockId ≟ b ∙blockId
... | no _
  = there $ IH p∈
... | yes b♯≡
  with p′ ∈? votes' b (s .history)
... | yes _
  = there $ IH p∈
... | no _
  with p∈
... | there ≪p∈ = there $ IH ≪p∈
... | here p≡ = here (p≡ , sym (♯-inj b♯≡))

honestVote⇒StepVotes : ∀ {s} (Rs : Reachable s) →
  p ∈ honestVotes b (s . history)
  ───────────────────────────────
  Rs ∋⋯ StepVotes p b
honestVote⇒StepVotes {s = s} Rs p∈ = let ms = s .history in
  honest∈votes⇒StepVotes Rs
    (L.All.lookup (Honest-honestVotes _ ms) p∈)
    (proj₁ $ L.Mem.∈-filter⁻ honest? {xs = votes _ ms}
           $ subst (_ ∈_) (honestVotes≡ _ ms) p∈)

GCB⇒votes :  ∀ {s} → Reachable s →
  GloballyCertifiedBlockIn s b
  ───────────────────────────────────────────
  ∃ λ p → Honest p × p ∈ votes b (s. history)
GCB⇒votes Rs gcb@(qc , cb , qc∈)
  with p , p∈ , hp ← qc⇒hp qc
  = p , hp , qc⇒vote ⦃ hp ⦄ Rs qc∈ p∈ cb
