{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.State.Invariants (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.State.Messages ⋯

open L.Mem

-- ** monotonicity

history-mono₁ :
  s′ ¹←— s
  ─────────────────────────
  s .history ⊆ˢ s′ .history
history-mono₁ (WaitUntil _ _ _) = id
history-mono₁ (Deliver _) = id
history-mono₁ (DishonestLocalStep _ _) = there
history-mono₁ (LocalStep st) with st
... | InitTC _ _ = there
... | InitNoTC _ _ = id
... | ProposeBlock _ _ = there
... | ProposeBlockNoOp _ _ = id
... | RegisterProposal _ _ _ _ _ = id
... | EnoughTimeouts _ _ _ _ = there
... | RegisterTimeout _ _ _ _ = id
... | RegisterTC _ _ _ _ = id
... | TimerExpired _ _ = there
... | RegisterVote _ _ _ _ _ _ = id
... | AdvanceRoundQC _ _ _ = id
... | AdvanceRoundTC _ _ _ = id
... | AdvanceRoundNoOp _ _ _ = id
... | Lock _ _ = id
... | Commit _ _ = id
... | CommitNoOp _ _ = id
... | VoteBlock _ _ _ = there
... | VoteBlockNoOp _ _ = id

b-history-mono₁ :
  ∙ s′ ¹←— s
  ∙ b ∙∈ s .history
    ─────────────────
    b ∙∈ s′ .history
b-history-mono₁ s← = ⊆-allBlocks⁺ $ history-mono₁ s←

ch-history-mono₁ :
  ∙ s′ ¹←— s
  ∙ ch ∙∈ s .history
    ─────────────────
    ch ∙∈ s′ .history
ch-history-mono₁ s← = λ where
  []              → []
  (b∈ ∷ ch∈ ⊣ b↝) → b-history-mono₁ s← b∈ ∷ ch-history-mono₁ s← ch∈ ⊣ b↝

history-mono :
  s′ ↞— s
  ─────────────────────────
  s .history ⊆ˢ s′ .history
history-mono = λ where
  (_ ∎)            → id
  (_ ⟨ →s′ ⟩←— s↠) → history-mono₁ →s′ ∘ history-mono s↠

b-history-mono :
  ∙ s′ ↞— s
  ∙ b ∙∈ s .history
    ────────────────
    b ∙∈ s′ .history
b-history-mono s← = ⊆-allBlocks⁺ $ history-mono s←

ch-history-mono :
  ∙ s′ ↞— s
  ∙ ch ∙∈ s .history
    ────────────────
    ch ∙∈ s′ .history
ch-history-mono s← = λ where
  []              → []
  (b∈ ∷ ch∈ ⊣ b↝) → b-history-mono s← b∈ ∷ ch-history-mono s← ch∈ ⊣ b↝

-- ** inclusion

net⊆history : ∀ {s} → Reachable s →
  (t , p , m) ∈ s .networkBuffer
  ──────────────────────────
  m ∈ s .history
net⊆history (_ , refl , (_ ∎)) ()
net⊆history {t}{p}{m} (s₀ , s-init , (s' ⟨ WaitUntil _ _ _ ∣ s ⟩←— tr)) pm∈
  = net⊆history {t}{p}{m} (_ , s-init , tr) pm∈
net⊆history {t}{p}{m} (s₀ , s-init , (s' ⟨ Deliver {tpm} tpm∈ ∣ s ⟩←— tr)) pm∈
  with Rs ← _ , s-init , tr
  with IH ← net⊆history {t}{p}{m} Rs
  = m∈
  where
  m∈ : m ∈ s .history
  m∈ = IH (∈-removeAt⁻ (L.Any.index tpm∈) pm∈)
net⊆history {t}{p}{m} (s₀ , s-init , (s' ⟨ DishonestLocalStep {env = env} {p = p′} ¬hp′ st ∣ s ⟩←— tr))
  tpm∈
  with Rs ← (_ , s-init , tr)
  with IH ← net⊆history {t}{p}{m} Rs
  with L.Mem.∈-++⁻ (s .networkBuffer) tpm∈
... | inj₁ tpm∈
  = there $ IH tpm∈
... | inj₂ tpm∈
  = here $ L.All.lookup (expandEnv-content≡ (s .currentTime) env) tpm∈
net⊆history {t}{p}{m} (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {ls′ = ls′} st ∣ s ⟩←— tr))
  tpm∈
  with Rs ← (_ , s-init , tr)
  with IH ← net⊆history {t}{p}{m} Rs
  with st
... | InitTC _ _
  = m∈
  where
  m∈ : m ∈ s' .history
  m∈ with ∈-++⁻ (s .networkBuffer) tpm∈
  ... | inj₁ tpm∈ = there $ IH tpm∈
  ... | inj₂ (here refl) = here refl
... | InitNoTC _ _
  = IH tpm∈
... | ProposeBlock _ _
  = m∈
  where
  m∈ : m ∈ s' .history
  m∈ with ∈-++⁻ (s .networkBuffer) tpm∈
  ... | inj₁ tpm∈ = there $ IH tpm∈
  ... | inj₂ tpm∈ = here (expandBroadcasts-message tpm∈)
... | ProposeBlockNoOp _ _
  = IH tpm∈
... | RegisterProposal m∈inbox _ _ _ _
  = IH tpm∈
... | EnoughTimeouts m∈inbox _ _ _
  = m∈
  where
  m∈ : m ∈ s' .history
  m∈ with ∈-++⁻ (s .networkBuffer) tpm∈
  ... | inj₁ tpm∈ = there $ IH tpm∈
  ... | inj₂ tpm∈ = here (expandBroadcasts-message tpm∈)
... | RegisterTimeout m∈inbox _ _ _
  = IH tpm∈
... | RegisterTC m∈inbox _ _ _
  = IH tpm∈
... | TimerExpired _ _
  = m∈
  where
  m∈ : m ∈ s' .history
  m∈ with ∈-++⁻ (s .networkBuffer) tpm∈
  ... | inj₁ tpm∈ = there $ IH tpm∈
  ... | inj₂ tpm∈ = here (expandBroadcasts-message tpm∈)
... | RegisterVote m∈inbox _ _ _ _ _
  = IH tpm∈
... | AdvanceRoundQC _ _ _
  = IH tpm∈
... | AdvanceRoundTC _ _ _
  = IH tpm∈
... | AdvanceRoundNoOp _ _ _
  = IH tpm∈
... | Lock _ _
  = IH tpm∈
... | Commit _ _
  = IH tpm∈
... | CommitNoOp _ _
  = IH tpm∈
... | VoteBlock _ _ _
  = m∈
  where
  m∈ : m ∈ s' .history
  m∈ with ∈-++⁻ (s .networkBuffer) tpm∈
  ... | inj₁ tpm∈ = there $ IH tpm∈
  ... | inj₂ (here refl) = here refl
... | VoteBlockNoOp _ _
  = IH tpm∈

inbox⊆history : ∀ {s} ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .inbox ⊆ˢ s .history
inbox⊆history {p = p} (_ , refl , (_ ∎)) {m} ≪m∈
  rewrite pLookup-replicate p initLocalState
  = contradict ≪m∈
inbox⊆history {p = p} (s₀ , s-init , (s' ⟨ WaitUntil _ _ _ ∣ s ⟩←— tr)) {m} ≪m∈
  with Rs ← _ , s-init , tr
  = inbox⊆history Rs ≪m∈
inbox⊆history {p = p} (s₀ , s-init , (s' ⟨ Deliver {tpm} (tpm∈) ∣ s ⟩←— tr)) {m} ≪m∈
  with Rs ← _ , s-init , tr
  with IH ← inbox⊆history Rs
  --with IH-net ← (λ {p} → net⊆history {t}{p = p} {s = s} Rs)
  = m∈
  where
  receiveMsg-inbox : ∀ {s} tpm →
    let
        s' = receiveMsg s (honestTPMessage tpm)
        t , p′ , m′ = tpm
    in
    m ∈ (s' ＠ᵐ p) .inbox
    ─────────────────────────
      m ∈ (s ＠ᵐ p) .inbox
    ⊎ ((p , m) ≡ (p′ , m′))
--  receiveMsg-inbox nothing m∈ = inj₁ m∈
  receiveMsg-inbox {s} (t′ , p′ , m) m∈
    with honest? p′
  ... | no _ = inj₁ m∈
  ... | yes hp′
    with p ≟ p′
  ... | no p≢
    rewrite let instance _ = hp′ in
            pLookup∘updateAt′ p p′ {receiveMessage m} (p≢ ∘ ↑-injective) s
    = inj₁ m∈
  ... | yes refl
    rewrite pLookup∘updateAt p {receiveMessage m} s
    = case L.Mem.∈-++⁻ ((s ＠ᵐ p) .inbox) m∈ of λ where
      (inj₁ m∈)          → inj₁ m∈
      (inj₂ (here refl)) → inj₂ $ refl
  m∈ : m ∈ s .history
  m∈ = case receiveMsg-inbox tpm ≪m∈ of λ where
    (inj₁ m∈inbox) → IH m∈inbox
    (inj₂ refl)    → net⊆history Rs tpm∈
inbox⊆history {p = p} ⦃ hp ⦄ (_ , s-init , (s' ⟨ LocalStep {p = p′} {ls′ = ls′} ⦃ hp′ ⦄ st ∣ s ⟩←— tr))
  {m} m∈
  with Rs ← (_ , s-init , tr)
  with IH ← inbox⊆history {p = p} Rs
  with p ≟ p′
... | no p≢
  rewrite let instance _ = hp′ in
          pLookup∘updateAt′ p p′ ⦃ hp′ ⦄ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  =  L.Mem.∈-++⁺ʳ _ $ IH m∈
... | yes refl
  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st
... | InitTC _ _ = there $ IH m∈
... | InitNoTC _ _ = IH m∈
... | ProposeBlock _ _ = there $ IH m∈
... | ProposeBlockNoOp _ _ = IH m∈
... | RegisterProposal m∈inbox _ _ _ _ = IH $ ∈-removeAt⁻ _ m∈
... | EnoughTimeouts m∈inbox _ _ _ = there $ IH m∈
... | RegisterTimeout m∈inbox _ _ _ = IH $ ∈-removeAt⁻ _ m∈
... | RegisterTC m∈inbox _ _ _ = IH $ ∈-removeAt⁻ _ m∈
... | TimerExpired _ _ = there $ IH m∈
... | RegisterVote m∈inbox _ _ _ _ _ = IH $ ∈-removeAt⁻ _ m∈
... | AdvanceRoundQC _ _ _ = IH m∈
... | AdvanceRoundTC _ _ _ = IH m∈
... | AdvanceRoundNoOp _ _ _ = IH m∈
... | Lock _ _ = IH m∈
... | Commit _ _ = IH m∈
... | CommitNoOp _ _ = IH m∈
... | VoteBlock _ _ _ = there $ IH m∈
... | VoteBlockNoOp _ _ = IH m∈
inbox⊆history {p = p} (_ , s-init , (_ ⟨ DishonestLocalStep _ _ ⟩←— tr))
  {m} m∈
  with Rs ← (_ , s-init , tr)
  with IH ← inbox⊆history {p = p} Rs
  = there $ IH m∈

db⊆history : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ls .db ⊆ˢ s .history
db⊆history {p = p} (_ , refl , (_ ∎)) {m} ≪m∈
  rewrite pLookup-replicate p initLocalState
  = contradict ≪m∈
db⊆history (s , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr)) {m} ≪m∈
  = db⊆history (_ , s-init , tr) ≪m∈
db⊆history (s , s-init , (_ ⟨ Deliver {tpm} _ ⟩←— tr)) {m} ≪m∈
  = db⊆history (s , s-init , tr) (subst (_ ∈_) (receiveMsg-db (honestTPMessage tpm)) ≪m∈)
db⊆history (s , s-init , (_ ⟨ DishonestLocalStep _ _ ⟩←— tr)) {m} ≪m∈
  = there $ db⊆history (s , s-init , tr) ≪m∈
db⊆history {p = p}  ⦃ hp ⦄ (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {ls′ = ls′}  ⦃ hp′ ⦄ st ∣ s ⟩←— tr))
  {m} ≪m∈
  with Rs ← (_ , s-init , tr)
  with IH ← db⊆history {p = p} Rs
  with lookup✓ ← pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with lookup✖ ← (λ p≢ → pLookup∘updateAt′ p p′ ⦃ hp′ ⦄ {const ls′} (p≢ ∘ ↑-injective {∃p =  p ,· hp} {∃p′ = p′ ,· hp′}) (s .stateMap))
  with st
... | InitTC _ _
  = there $ IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | InitNoTC _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | ProposeBlock _ _
  = there $ IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | ProposeBlockNoOp _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | RegisterProposal m∈inbox _ _ _ _
  = m∈
  where
  m∈ : m ∈ s .history
  m∈ with p ≟ p′
  ... | no  p≢   rewrite lookup✖ p≢ = IH ≪m∈
  ... | yes refl rewrite lookup✓
    with ⟫ ≪m∈
  ... | ⟫ here refl = inbox⊆history ⦃ hp ⦄ Rs m∈inbox
  ... | ⟫ there ≪m∈ = IH ≪m∈
... | EnoughTimeouts m∈inbox _ _ _
  = there $ IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | RegisterTimeout m∈inbox _ _ _
  = m∈
  where
  m∈ : m ∈ s .history
  m∈ with p ≟ p′
  ... | no  p≢   rewrite lookup✖ p≢ = IH ≪m∈
  ... | yes refl rewrite lookup✓
    with ⟫ ≪m∈
  ... | ⟫ here refl = inbox⊆history ⦃ hp ⦄ Rs m∈inbox
  ... | ⟫ there ≪m∈ = IH ≪m∈
... | RegisterTC m∈inbox _ _ _
  = m∈
  where
  m∈ : m ∈ s .history
  m∈ with p ≟ p′
  ... | no  p≢   rewrite lookup✖ p≢ = IH ≪m∈
  ... | yes refl rewrite lookup✓
    with ⟫ ≪m∈
  ... | ⟫ here refl = inbox⊆history ⦃ hp ⦄ Rs m∈inbox
  ... | ⟫ there ≪m∈ = IH ≪m∈
... | TimerExpired _ _
  = there $ IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | RegisterVote m∈inbox _ _ _ _ _
  = m∈
  where
  m∈ : m ∈ s .history
  m∈ with p ≟ p′
  ... | no  p≢   rewrite lookup✖ p≢ = IH ≪m∈
  ... | yes refl rewrite lookup✓
    with ⟫ ≪m∈
  ... | ⟫ here refl = inbox⊆history ⦃ hp ⦄ Rs m∈inbox
  ... | ⟫ there ≪m∈ = IH ≪m∈
... | AdvanceRoundQC _ _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | AdvanceRoundTC _ _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | AdvanceRoundNoOp _ _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | Lock _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | Commit _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | CommitNoOp _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | VoteBlock _ _ _
  = there $ IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈
... | VoteBlockNoOp _ _
  = IH m∈
  where
  m∈ : m ∈ (s ＠ p) .db
  m∈ with p ≟ p′
  ... | yes refl rewrite lookup✓    = ≪m∈
  ... | no  p≢   rewrite lookup✖ p≢ = ≪m∈

b-db⊆history : ∀ {s} →  ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  b ∙∈ ls .db
  ────────────────
  b ∙∈ s .history
b-db⊆history Rs = ⊆-allBlocks⁺ (db⊆history Rs)

ch-db⊆history : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ch ∙∈ ls .db
  ────────────────
  ch ∙∈ s .history
ch-db⊆history Rs = λ where
  []              → []
  (b∈ ∷ ch∈ ⊣ b↝) → b-db⊆history Rs b∈ ∷ ch-db⊆history Rs ch∈ ⊣ b↝

qc-db⊆history : ∀ {s} →  ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  qc ∙∈ ls .db
  ────────────────
  qc ∙∈ s .history
qc-db⊆history {qc = qc} {s = s} Rs = λ where
  (initialQC gen≡)  → initialQC gen≡
  (formedQC ≪fqc)   → formedQC {qc = qc} $ L.All.map (db⊆history Rs) ≪fqc
  (receivedQC ≪qc∈) → let m , qc∈ , m∈ = Any⇒∃ ≪qc∈
                      in receivedQC $ ∃⇒Any (m , qc∈ , db⊆history Rs m∈)

tc-db⊆history : ∀ {s} →  ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  tc ∙∈ ls .db
  ────────────────
  tc ∙∈ s .history
tc-db⊆history {tc = tc} {s = s} Rs = λ where
  (formedTC ≪ftc)   → formedTC {tc = tc} $ L.All.map (map₂ $ db⊆history Rs) ≪ftc
  (receivedTC ≪tc∈) → let m , tc∈ , m∈ = Any⇒∃ ≪tc∈
                      in receivedTC $ ∃⇒Any (m , tc∈ , db⊆history Rs m∈)

-- -- ** qc-high

qc-high∈db : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ─────────────────────
  ls .qc-high ∙∈ ls .db
qc-high∈db {p} (_ , refl , (_ ∎))
  rewrite pLookup-replicate p initLocalState
  = initialQC refl
qc-high∈db {p} (_ , s-init , (s' ⟨ WaitUntil _ _ _ ∣ s ⟩←— tr))
  = qc-high∈db (_ , s-init , tr)
qc-high∈db {p} (_ , s-init , (s' ⟨ Deliver {tpm} _ ∣ s ⟩←— tr))
  = subst (_∙∈ (s' ＠ p) .db)     (sym $ receiveMsg-qcHigh (honestTPMessage tpm))
  $ subst ((s ＠ p) .qc-high ∙∈_) (sym $ receiveMsg-db (honestTPMessage tpm))
  $ qc-high∈db (_ , s-init , tr)
qc-high∈db {p} (_ , s-init , (s' ⟨ DishonestLocalStep _ _ ∣ s ⟩←— tr))
  = qc-high∈db (_ , s-init , tr)
qc-high∈db {p} ⦃ hp ⦄
  (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {menv = menv} {ls′ = ls′} st ∣ s ⟩←— tr))
  with Rs ← _ , s-init , tr
  with IH ← qc-high∈db {p} Rs
  with p ≟ p′
... | no p≢    rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap) = IH
... | yes refl rewrite pLookup∘updateAt  p ⦃ hp ⦄   {const ls′}    (s .stateMap)
  with st
... | InitTC _ _ = IH
... | InitNoTC _ _ = IH
... | ProposeBlockNoOp _ _ = IH
... | RegisterProposal _ _ _ _ _ = qc∈-monotonic IH
... | EnoughTimeouts _ _ _ _ = IH
... | RegisterTimeout _ _ _ _ = qc∈-monotonic IH
... | RegisterTC _ _ _ _ = qc∈-monotonic IH
... | TimerExpired _ _ = IH
... | RegisterVote _ _ _ _ _ _ = qc∈-monotonic IH
... | AdvanceRoundQC _ _ _ = IH
... | AdvanceRoundTC _ _ _ = IH
... | AdvanceRoundNoOp _ _ _ = IH
... | Lock _ (isHighest qc∈ _) = qc∈
... | CommitNoOp _ _ = IH
... | VoteBlock _ _ _ = IH
... | VoteBlockNoOp _ _ = IH
... | Commit _ _ = IH
... | ProposeBlock _ _ = IH

-- -- ** tc-last

tc-last∈history : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ──────────────────────────────────
  All (_∙∈ s .history) (ls .tc-last)
tc-last∈history {p} (_ , refl , (_ ∎))
  rewrite pLookup-replicate p initLocalState
  = nothing
tc-last∈history {p} (_ , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr))
  = tc-last∈history (_ , s-init , tr)
tc-last∈history {p} (_ , s-init , (_ ⟨ Deliver {tpm} _ ⟩←— tr))
  = subst (All _) (sym $ receiveMsg-tcLast (honestTPMessage tpm))
  $ tc-last∈history (_ , s-init , tr)
tc-last∈history {p} (_ , s-init , (s' ⟨ DishonestLocalStep _ _ ∣ s ⟩←— tr))
  = M.All.map (tc∈-++⁺ʳ {ms = [ _ ]}) $ tc-last∈history (_ , s-init , tr)
tc-last∈history {p} ⦃ hp ⦄
  (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {menv = menv} {ls′ = ls′} st ∣ s ⟩←— tr))
  with Rs ← _ , s-init , tr
  with IH ← tc-last∈history {p} Rs
  with p ≟ p′
... | no p≢    rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = M.All.map tc∈-++⁺ʳ IH
... | yes refl rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′}    (s .stateMap)
  with st
... | InitTC _ _ = M.All.map tc∈-monotonic IH
... | InitNoTC _ _ = IH
... | ProposeBlock _ _ = M.All.map tc∈-monotonic IH
... | ProposeBlockNoOp _ _ = IH
... | RegisterProposal _ _ _ _ _ = IH
... | EnoughTimeouts _ _ _ _ = M.All.map tc∈-monotonic IH
... | RegisterTimeout _ _ _ _ = IH
... | RegisterTC _ _ _ _ = IH
... | TimerExpired _ _ = M.All.map tc∈-monotonic IH
... | RegisterVote _ _ _ _ _ _ = IH
... | AdvanceRoundQC _ _ _ = nothing
... | AdvanceRoundTC _ tc∈ _ = just $ tc-db⊆history ⦃ hp ⦄ Rs tc∈
... | AdvanceRoundNoOp _ _ _ = IH
... | Lock _ _ = IH
... | CommitNoOp _ _ = IH
... | VoteBlock _ _ _ = M.All.map tc∈-monotonic IH
... | VoteBlockNoOp _ _ = IH
... | Commit _ _ = IH

tc-last-r≡ : ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ────────────────────────────────────────────────────
  All (λ tc → ls .r-cur ≡ 1 + tc ∙round) (ls .tc-last)
tc-last-r≡ {p} (_ , refl , (_ ∎))
  rewrite pLookup-replicate p initLocalState
  = nothing
tc-last-r≡ {p} (_ , s-init , (_ ⟨ WaitUntil _ _ _ ⟩←— tr))
  = tc-last-r≡ (_ , s-init , tr)
tc-last-r≡ {p} (_ , s-init , (_ ⟨ Deliver {tpm} _ ⟩←— tr))
  = subst (All _) (sym $ receiveMsg-tcLast (honestTPMessage tpm))
  $ M.All.map (subst (_≡ _) $ sym $ receiveMsg-rCur (honestTPMessage tpm))
  $ tc-last-r≡ (_ , s-init , tr)
tc-last-r≡ {p} (_ , s-init , (_ ⟨ DishonestLocalStep _ _ ⟩←— tr))
  = tc-last-r≡ (_ , s-init , tr)
tc-last-r≡ {p} ⦃ hp ⦄
  (s₀ , s-init , (s' ⟨ LocalStep {p = p′} {menv = menv} {ls′ = ls′} st ∣ s ⟩←— tr))
  with Rs ← _ , s-init , tr
  with IH ← tc-last-r≡ {p} Rs
  with p ≟ p′
... | no p≢    rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap)
  = IH
... | yes refl rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′}    (s .stateMap)
  with st
... | InitTC _ _ = IH
... | InitNoTC _ _ = IH
... | ProposeBlock _ _ = IH
... | ProposeBlockNoOp _ _ = IH
... | RegisterProposal _ _ _ _ _ = IH
... | EnoughTimeouts _ _ _ _ = IH
... | RegisterTimeout _ _ _ _ = IH
... | RegisterTC _ _ _ _ = IH
... | TimerExpired _ _ = IH
... | RegisterVote _ _ _ _ _ _ = IH
... | AdvanceRoundQC _ _ _ = nothing
... | AdvanceRoundTC _ tc∈ _ = just refl
... | AdvanceRoundNoOp _ _ _ = IH
... | Lock _ _ = IH
... | CommitNoOp _ _ = IH
... | VoteBlock _ _ _ = IH
... | VoteBlockNoOp _ _ = IH
... | Commit _ _ = IH

-- ** r-vote
r-vote-Bound :  ∀ {s} → ⦃ _ : Honest p ⦄ → Reachable s → let ls = s ＠ p in
  ────────────────────────────────────────────────────
  ls .r-vote ≤ 1 + ls .r-cur
r-vote-Bound {p} (_ , refl , (_ ∎))
  rewrite pLookup-replicate p initLocalState
  = Nat.z≤n
r-vote-Bound {p} ⦃ hp ⦄ (_ , s-init , (s' ⟨ st ∣ s ⟩←— tr))
  with IH ← r-vote-Bound {p} (_ , s-init , tr)
  with st
... | WaitUntil _ _ _
  = IH
... | Deliver {tpm} _
  rewrite receiveMsg-ls≡ {p}{s .stateMap} (honestTPMessage tpm)
  = IH
... | DishonestLocalStep _ _
  = IH
... | LocalStep {p = p′}{ls′ = ls′} st
  with p ≟ p′
... | no p≢    rewrite pLookup∘updateAt′ p p′ {const ls′} (p≢ ∘ ↑-injective) (s .stateMap) = IH
... | yes refl rewrite pLookup∘updateAt  p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with st
... | InitTC _ _ = IH
... | InitNoTC _ _ = IH
... | ProposeBlockNoOp _ _ = IH
... | RegisterProposal _ _ _ _ _ = IH
... | EnoughTimeouts _ _ _ _ = Nat.≤-refl
... | RegisterTimeout _ _ _ _ = IH
... | RegisterTC _ _ _ _ = IH
... | TimerExpired _ _ = Nat.≤-refl
... | RegisterVote _ _ _ _ _ _ = IH
... | AdvanceRoundQC _ _ qc≥ = Nat.≤-trans IH $ Nat.≤-trans (Nat.s≤s qc≥) (Nat.n≤1+n _)
... | AdvanceRoundTC _ _ tc≥ = Nat.≤-trans IH $ Nat.≤-trans (Nat.s≤s tc≥) (Nat.n≤1+n _)
... | AdvanceRoundNoOp _ _ _ = IH
... | Lock _ _ = IH
... | CommitNoOp _ _ = IH
... | VoteBlock _ _ _ = Nat.n≤1+n _
... | VoteBlockNoOp _ _ = IH
... | Commit _ _ = IH
... | ProposeBlock _ _ = IH
