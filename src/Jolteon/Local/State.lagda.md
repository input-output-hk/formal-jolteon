
# Local state from the view of a single node.

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Local.State (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
open import Jolteon.Message ⋯
```
-->

The different transition phases, i.e. the nodes in the state machine diagram.
```agda
data Phase : Type where
  EnteringRound Proposing Receiving AdvancingRound Locking Committing Voting : Phase
```
<!--
```agda
instance
  DecEq-Phase : DecEq Phase
  DecEq-Phase ._≟_ = λ where
    EnteringRound EnteringRound → yes refl
    EnteringRound Proposing → no λ ()
    EnteringRound Receiving → no λ ()
    EnteringRound AdvancingRound → no λ ()
    EnteringRound Locking → no λ ()
    EnteringRound Committing → no λ ()
    EnteringRound Voting → no λ ()

    Receiving EnteringRound → no λ ()
    Receiving Proposing → no λ ()
    Receiving Receiving → yes refl
    Receiving AdvancingRound → no λ ()
    Receiving Locking → no λ ()
    Receiving Committing → no λ ()
    Receiving Voting → no λ ()

    Proposing EnteringRound → no λ ()
    Proposing Proposing → yes refl
    Proposing Receiving → no λ ()
    Proposing AdvancingRound → no λ ()
    Proposing Locking → no λ ()
    Proposing Committing → no λ ()
    Proposing Voting → no λ ()

    AdvancingRound EnteringRound → no λ ()
    AdvancingRound Proposing → no λ ()
    AdvancingRound Receiving → no λ ()
    AdvancingRound AdvancingRound → yes refl
    AdvancingRound Locking → no λ ()
    AdvancingRound Committing → no λ ()
    AdvancingRound Voting → no λ ()

    Locking EnteringRound → no λ ()
    Locking Proposing → no λ ()
    Locking Receiving → no λ ()
    Locking AdvancingRound → no λ ()
    Locking Locking → yes refl
    Locking Committing → no λ ()
    Locking Voting → no λ ()

    Committing EnteringRound → no λ ()
    Committing Proposing → no λ ()
    Committing Receiving → no λ ()
    Committing AdvancingRound → no λ ()
    Committing Locking → no λ ()
    Committing Committing → yes refl
    Committing Voting → no λ ()

    Voting EnteringRound → no λ ()
    Voting Proposing → no λ ()
    Voting Receiving → no λ ()
    Voting AdvancingRound → no λ ()
    Voting Locking → no λ ()
    Voting Committing → no λ ()
    Voting Voting → yes refl
```
-->

Furthermore, the local state stores a database of blocks and votes,
an inbox for unread messages, and the current finalized chain.

```agda
record LocalState : Type where
  constructor ⦅_,_,_,_,_,_,_,_,_,_,_⦆
  field
    r-vote    : Round     -- highest voted round
    -- r-lock    : Round     -- highest locked round
    r-cur     : Round     -- current round
    qc-high   : QC        -- highest quorum certificate
    tc-last   : Maybe TC  -- last round timeout certificate

    phase      : Phase     -- current phase
    db         : Messages  -- list of processed messages
    inbox      : Messages  -- messages received, but not yet processed
    finalChain : Chain     -- the most recent committed chain

    timer      : Maybe Time -- (optional) timer to fire
    timedOut?  : Bool       -- whether the timer has fired

    roundAdvanced? : Bool -- whether the round has advanced

  currentLeader = roundLeader r-cur
  nextLeader    = roundLeader (1 + r-cur)

  timedOut : Time → Type
  timedOut t = Any (_≤ t) timer
```
<!--
```agda
open LocalState public
variable ls ls′ ls″ : LocalState
```
-->

The initial local state is the empty one:
```agda
initLocalState : LocalState
initLocalState = record
  { r-vote = 0
  -- ; r-lock = 0
  ; r-cur = 1
  ; qc-high = qc₀
  ; tc-last = nothing
  ; phase = EnteringRound
  ; db = []
  ; inbox = []
  ; finalChain = []
  ; timer =  nothing
  ; timedOut? = false
  ; roundAdvanced? = true
  }
```
<!--
```agda
instance
  Def-LocalState  = Default _ ∋ λ where .def → initLocalState
  Init-LocalState = HasInitial _ ∋ λ where .Initial → _≡ initLocalState

mkBlockForState : LocalState → List Transaction → Block
mkBlockForState ls txs = ⟨ ls .qc-high , ls .tc-last , ls .r-cur , txs {-⊣ {!!}-} ⟩

instance
  DecEq-LocalState : DecEq LocalState
  DecEq-LocalState ._≟_ s s′
    with s .r-vote ≟ s′ .r-vote
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .r-cur ≟ s′ .r-cur
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .qc-high ≟ s′ .qc-high
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .tc-last ≟ s′ .tc-last
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .phase ≟ s′ .phase
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .db ≟ s′ .db
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .inbox ≟ s′ .inbox
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .finalChain ≟ s′ .finalChain
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .timer ≟ s′ .timer
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .timedOut? ≟ s′ .timedOut?
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
    with s .roundAdvanced? ≟ s′ .roundAdvanced?
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl
      = yes refl
```
-->

## Blocks and Chains contained within messages

### Membership class

```agda
record Has∈ (A : Type) : Type₁ where
  field _∙∈_ : A → Messages → Type
  _∙∉_ = ¬_ ∘₂ _∙∈_
  infix 100 _∙∈_

  module _ ⦃ _ : _∙∈_ ⁇² ⦄ where
    _∙∈?_ : Decidable² _∙∈_
    _∙∈?_ = dec²
open Has∈ ⦃...⦄ public

data AllMs {A} ⦃ _ : Has∈ A ⦄ (P : A → Type) (ms : Messages) : Type where
  mk : (∀ {a} → a ∙∈ ms → P a) → AllMs P ms
```

### Block Membership

```agda
{-
data _-block-∈-_ : Block → Messages → Type where
  initialBlock :
    b ∙blockId ≡ genesisId
    ──────────────────────
    b -block-∈- ms

  proposedBlock :
    b ∈ allBlocks ms
    ────────────────
    b -block-∈- ms

  -- In the paper there's no other way of learning about a block.
  -- inQC :
  --     ∙ Any (qc qc∈-Message_) ms
  --     ∙ qc ∙blockId ≡ b ∙blockId
  --     ───────────────────────────
  --     b block-∈ ms

instance Has∈-Block = Has∈ Block ∋ λ where ._∙∈_ → _-block-∈-_
-}

instance Has∈-Block = Has∈ Block ∋ λ where ._∙∈_ b ms → b ∈ allBlocks ms
```

We define different Predicates on chains wrt to lists of messages.


### QC membership

```agda
qcVoteShares : QC → VoteShares
qcVoteShares qc = map (qc .payload signed-by_) (qc .shares)
```
<!--
```agda
qcVoteShares-All : (qc : QC) → All (λ d → qc .payload ≡ d .datum) (qcVoteShares qc)
qcVoteShares-All qc = L.All.map⁺ (L.All.tabulate (λ _ → refl))
```
-->
```agda
instance Has∈-VS = Has∈ VoteShare ∋ λ where ._∙∈_ vs ms → Vote vs ∈ ms

FormedVS : VoteShares → Messages → Type
FormedVS vss ms = All (_∙∈ ms) vss

FormedQC : QC → Messages → Type
FormedQC qc = FormedVS (qcVoteShares qc)

data _-qc-∈-_ (qc : QC) (ms : Messages) : Type where
  initialQC :
    qc ≡ qc₀
    ────────────
    qc -qc-∈- ms

  formedQC :
    FormedQC qc ms -- all voteshares come from ms
    ──────────────
    qc -qc-∈- ms

  receivedQC :
    Any (qc qc∈-Message_) ms
    ────────────────────────
    qc -qc-∈- ms
```

### TC Membership

```agda
_-te-∈-_ : TimeoutEvidence → Messages → Type
te -te-∈- ms = ∃ λ mtc → Timeout (te , mtc) ∈ ms

instance Has∈-TimeoutEvidence = Has∈ TimeoutEvidence ∋ λ where ._∙∈_ → _-te-∈-_

FormedTE : List TimeoutEvidence → Messages → Type
FormedTE tes ms = All (_∙∈ ms) tes

FormedTC : TC → Messages → Type
FormedTC tc = FormedTE (tc .tes)

data _-tc-∈-_ (tc : TC) (ms : Messages) : Type where
  formedTC :
    FormedTC tc ms
    ──────────────────────
    tc -tc-∈- ms

  receivedTC :
    Any (tc tc∈-Message_) ms
    ────────────────────────
    tc -tc-∈- ms
```
<!--
```agda
instance
  Has∈-QC = Has∈ QC ∋ λ where ._∙∈_ → _-qc-∈-_
  Has∈-TC = Has∈ TC ∋ λ where ._∙∈_ → _-tc-∈-_

AllQC    = AllMs {A = QC}
AllTC    = AllMs {A = TC}
AllBlock = AllMs {A = Block}
NoBlock  = AllBlock ∘ ∁

-- ** properties of qc-∈

qc∈-monotonic :
  qc ∙∈ ms
  ──────────────
  qc ∙∈ (m ∷ ms)
qc∈-monotonic = λ where
  (initialQC eq)   → initialQC eq
  (formedQC p)     → formedQC $ L.All.map there p
  (receivedQC qc∈) → receivedQC $ there qc∈

qc∈-++⁺ʳ :
  qc ∙∈ ms′
  ─────────────────
  qc ∙∈ (ms ++ ms′)
qc∈-++⁺ʳ {ms = []}     = id
qc∈-++⁺ʳ {ms = _ ∷ ms} = qc∈-monotonic ∘ qc∈-++⁺ʳ {ms = ms}

¬FormedQC-[] : ∀ qc → ¬ FormedQC qc []
¬FormedQC-[] qc fqc
  with qcVoteShares qc in qcVS≡ | fqc
... | _ ∷ _ | () ∷ _
... | []    | _
    = ⊥-elim
    $ majority⁺ $ subst IsMajority (Null-map⁻ qcVS≡) (getQuorum qc)

only-qc₀ :
  qc ∙∈ []
  ────────
  qc ≡ qc₀
only-qc₀ (initialQC refl) = refl
only-qc₀ {qc} (formedQC fqc) = ⊥-elim $ ¬FormedQC-[] qc fqc

b∈⇒qc∈ :
  b ∙∈ ms
  ────────────────
  b .blockQC ∙∈ ms
b∈⇒qc∈ {ms = ms} b∈
  with sb , sb∈ , refl ← ∈-allBlocks⁻ {ms = ms} b∈
  with p∈ ← ∈-allSBlocks⁻ sb∈
  = receivedQC $ L.Any.map (λ where refl → qc∈-Propose refl) p∈

qc∉∈-TC : let m = TCFormed tc in
  ∙ qc ∙∉ ms
  ∙ qc ∙∈ (m ∷ ms)
    ────────────────
    qc qc∈-Message m
qc∉∈-TC qc∉ (initialQC gen) = ⊥-elim $ qc∉ (initialQC gen)
qc∉∈-TC qc∉ (formedQC qtc) =
  ⊥-elim $ qc∉ $ formedQC (L.All.map (λ where (there p) → p) qtc)
qc∉∈-TC qc∉ (receivedQC m∈) = case m∈ of λ where
  (here px)  → px
  (there m∈) → ⊥-elim $ qc∉ $ receivedQC m∈

qc∉∈-Propose : let m = Propose sb in
  ∙ qc ∙∉ ms
  ∙ qc ∙∈ (m ∷ ms)
    ────────────────
    qc qc∈-Message m
qc∉∈-Propose qc∉ (initialQC gen) = ⊥-elim $ qc∉ (initialQC gen)
qc∉∈-Propose qc∉ (formedQC qtc) =
  ⊥-elim $ qc∉ $ formedQC (L.All.map (λ where (there p) → p) qtc)
qc∉∈-Propose qc∉ (receivedQC m∈) = case m∈ of λ where
  (here px)  → px
  (there m∈) → ⊥-elim $ qc∉ $ receivedQC m∈

qc∉∈-Timeout : let m = Timeout tm in
  ∙ qc ∙∉ ms
  ∙ qc ∙∈ (m ∷ ms)
    ────────────────
    qc qc∈-Message m
qc∉∈-Timeout qc∉ (initialQC gen) = ⊥-elim $ qc∉ (initialQC gen)
qc∉∈-Timeout qc∉ (formedQC qtc) =
  ⊥-elim $ qc∉ $ formedQC (L.All.map (λ where (there p) → p) qtc)
qc∉∈-Timeout qc∉ (receivedQC m∈) = case m∈ of λ where
  (here px)  → px
  (there m∈) → ⊥-elim $ qc∉ $ receivedQC m∈

qc∉∈-FormedVS : ∀ {vs vss} → let m = Vote vs in
  ∙ Unique vss
  ∙ ¬ FormedVS vss ms
  ∙ FormedVS vss (m ∷ ms)
    ───────────────────────
    Σ[ p ∈ (vs ∈ vss) ]
      FormedVS (vss ─ p) ms
qc∉∈-FormedVS {ms = ms} {vss = vss} uniqVss ¬qtc qtc
  with ∃vs ← L.All.¬All⇒Any¬ (_∙∈? ms) _ ¬qtc
  -- ∃vs : Any (_∙∉ ms) vss
  with vs , vs∈ , vs∉ ← satisfied′ ∃vs
  -- vs∈ : vs ∈ vss
  -- vs∉ : vs ∙∉ ms
  with m∈ ← L.All.lookup qtc vs∈
  -- m∈ : vs ∙∈ (m ∷ ms)
  with m∈
... | there vs∈
  = ⊥-elim $ vs∉ vs∈
... | here refl
  = vs∈ , L.All.tabulate QED
  where
  vs∉─ : vs ∉ (vss ─ vs∈)
  vs∉─ = ∉-─ id vs∈
       $ subst Unique (sym $ L.map-id vss) uniqVss

  QED : ∀ {vs} → vs ∈ (vss ─ vs∈) → vs ∙∈ ms
  QED {vs} vs∈─
    with L.All.lookup qtc {vs} (∈-─⁻ _ vs∈─)
  ... | there vs∈ = vs∈
  ... | here refl = ⊥-elim $ vs∉─ vs∈─

qc∉∈-FormedQC : ∀ {vs} → let m = Vote vs in
  ∙ ¬ FormedQC qc ms
  ∙ FormedQC qc (m ∷ ms)
    ───────────────────────────────────
    Σ[ p ∈ (vs ∈ qcVoteShares qc) ]
      FormedVS (qcVoteShares qc ─ p) ms
qc∉∈-FormedQC {qc = qc} ¬qtc qtc = qc∉∈-FormedVS uniqVss ¬qtc qtc
  where
  uniqVss : Unique (qcVoteShares qc)
  uniqVss = L.Unique.map⁺ (λ where refl → refl) (getUnique qc)

qc∉∈-Vote : ∀ {vs} → let m = Vote vs in
  ∙ qc ∙∉ ms
  ∙ qc ∙∈ (m ∷ ms)
    ───────────────────────────────────
    Σ[ p ∈ (vs ∈ qcVoteShares qc) ]
      FormedVS (qcVoteShares qc ─ p) ms
qc∉∈-Vote qc∉ (initialQC gen) = ⊥-elim $ qc∉ (initialQC gen)
qc∉∈-Vote {qc = qc} qc∉ (formedQC qtc) =
  qc∉∈-FormedQC {qc = qc} (qc∉ ∘ formedQC) qtc
qc∉∈-Vote qc∉ (receivedQC m∈) = case m∈ of λ where
  (here ())
  (there m∈) → ⊥-elim $ qc∉ $ receivedQC m∈

FormedQC-≢ : ∀ {vs} → let m = Vote vs in
  ∙ FormedQC qc (m ∷ ms)
  ∙ vs ∙blockId ≢ qc ∙blockId
    ─────────────────────────
    FormedQC qc ms
FormedQC-≢ {qc}{ms}{vs} fqc id≢
  using m ← Vote vs
  with ¿ FormedQC qc ms ¿
... | yes fqc = fqc
... | no ¬fqc
  using vs∈ , _ ← qc∉∈-FormedQC {qc} ¬fqc fqc
  rewrite L.All.lookup (qcVoteShares-All qc) vs∈
  = ⊥-elim $ id≢ refl

FormedQC-≡ : ∀ {vs} → let m = Vote vs in
  ∙ ¬ FormedQC qc ms
  ∙ FormedQC qc (m ∷ ms)
    ─────────────────────────
    qc .payload ≡ vs .datum
FormedQC-≡ {qc} ¬fqc fqc
  using vs∈ , fvs ← qc∉∈-FormedQC {qc} ¬fqc fqc
  = L.All.lookup (qcVoteShares-All qc) vs∈

-- ** properties of te-∈
te∈-monotonic :
  te ∙∈ ms
  ──────────────
  te ∙∈ (m ∷ ms)
te∈-monotonic = map₂ there

-- ** properties of tc-∈

tc∈-monotonic :
  tc ∙∈ ms
  ──────────────
  tc ∙∈ (m ∷ ms)
tc∈-monotonic = λ where
  (formedTC p)     → formedTC   $ L.All.map te∈-monotonic p
  (receivedTC tc∈) → receivedTC $ there tc∈

tc∈-++⁺ʳ :
  tc ∙∈ ms′
  ─────────────────
  tc ∙∈ (ms ++ ms′)
tc∈-++⁺ʳ {ms = []}     = id
tc∈-++⁺ʳ {ms = _ ∷ ms} = tc∈-monotonic ∘ tc∈-++⁺ʳ {ms = ms}

¬FormedTC-[] : ∀ tc → ¬ FormedTC tc []
¬FormedTC-[] tc ftc
  with tc .tes | ftc | getQuorumTC tc
... | .[]   | []           | maj = ⊥-elim $ majority⁺ maj
... | _ ∷ _ | (_ , ()) ∷ _ | _

tc∉-[] : tc ∙∉ []
tc∉-[] {tc} (formedTC ftc) = ¬FormedTC-[] tc ftc

tc∉∈-Propose : let m = Propose sb in
  ∙ tc ∙∉ ms
  ∙ tc ∙∈ (m ∷ ms)
    ────────────────
    tc tc∈-Message m
tc∉∈-Propose tc∉ (formedTC ftc) =
  ⊥-elim $ tc∉ $ formedTC $ L.All.map (λ where (_ , there te∈) → -, te∈) ftc
tc∉∈-Propose tc∉ (receivedTC m∈) = case m∈ of λ where
  (here px)  → px
  (there m∈) → ⊥-elim $ tc∉ $ receivedTC m∈

tc∉∈-Vote : ∀ {sv} → let m = Vote sv in
  ∙ tc ∙∉ ms
  ∙ tc ∙∈ (m ∷ ms)
    ────────────────
    tc tc∈-Message m
tc∉∈-Vote tc∉ (formedTC ftc) =
  ⊥-elim $ tc∉ $ formedTC $ L.All.map (λ where (_ , there te∈) → -, te∈) ftc
tc∉∈-Vote tc∉ (receivedTC m∈) = case m∈ of λ where
  (here px)  → px
  (there m∈) → ⊥-elim $ tc∉ $ receivedTC m∈

tc∉∈-TC : let m = TCFormed tc′ in
  ∙ tc ∙∉ ms
  ∙ tc ∙∈ (m ∷ ms)
    ────────────────
    tc tc∈-Message m
tc∉∈-TC tc∉ (formedTC ftc) =
  ⊥-elim $ tc∉ $ formedTC $ L.All.map (λ where (_ , there te∈) → -, te∈) ftc
tc∉∈-TC tc∉ (receivedTC m∈) = case m∈ of λ where
  (here px)  → px
  (there m∈) → ⊥-elim $ tc∉ $ receivedTC m∈

All-tes′ : ∀ {te} tes →
  ∀ (te∈ : te ∈ tes) →
  ∙ (te ∙qcTE) ∙∈ ms
  ∙ All (_∙∈ ms) (qcsTES $ tes ─ te∈)
    ─────────────────────────────────
    All (_∙∈ ms) (qcsTES tes)
All-tes′ (_ ∷ _)    (here refl)    te∈ tes∈       = te∈ ∷ tes∈
All-tes′ (_  ∷ tes) (there te∈tes) te∈ (p ∷ tes∈) = p   ∷ All-tes′ tes te∈tes te∈ tes∈

All-tes : let te = tm .proj₁ in
  ∀ (te∈ : te ∈ tc .tes) →
  ∙ (te ∙qcTE) ∙∈ ms
  ∙ All (_∙∈ ms) (qcsTES $ tc .tes ─ te∈)
    ─────────────────────────────────────
    All (_∙∈ ms) (qcs tc)
All-tes {tm}{tc} te∈tes te∈ tes∈
  = subst (All (_∙∈ _)) (sym $ qcs≡qcsTES tc)
  $ All-tes′ {te = tm .proj₁} (tc .tes) te∈tes te∈ tes∈

All-FormedTC :
   FormedTC tc ms   --All (_∙∈ ms) (tc .tes)
   ─────────────────────
   All (_∙∈ ms) (qcs tc)
   -- All (_∙∈ ms) (map _∙qcTE (tc . tes))
All-FormedTC {tc}{ms} ftc rewrite qcs≡qcsTES tc
  = L.All.map⁺ {f = _∙qcTE}
     (L.All.map (λ (mtc , m∈) → receivedQC (L.Any.map (λ where refl → qc∈-Timeout refl) m∈)) ftc)

All-tc∈ :
   tc tc∈-Message m
   ─────────────────────
   All (_qc∈-Message m) (qcs tc)
All-tc∈ (tc∈-Propose jtc≡) = L.All.tabulate (λ qc∈ → qc∈-ProposeTC jtc≡ qc∈)
All-tc∈ tc∈-TCFormed = L.All.tabulate qc∈-TCFormed
All-tc∈ (tc∈-Timeout jtc≡) = L.All.tabulate (qc∈-TimeoutTC jtc≡)

tc∈⇒qc∈ :
 ∙ tc ∙∈ ms
   ─────────────────────
   All (_∙∈ ms) (qcs tc)
tc∈⇒qc∈ {tc} (formedTC ftc) = All-FormedTC {tc} ftc
tc∈⇒qc∈ (receivedTC (here px)) = L.All.map (receivedQC ∘ here) $ All-tc∈ px
tc∈⇒qc∈ (receivedTC (there tc∈)) = L.All.map qc∈-monotonic $ tc∈⇒qc∈ (receivedTC tc∈)

module _ ⦃ _ : _-te-∈-_ ⁇² ⦄ where
  tc∉∈-FormedTE : ∀ {tes} → let m = Timeout tm; te = tm .proj₁ in
    ∙ UniqueBy node tes
    ∙ ¬ FormedTE tes ms
    ∙ FormedTE tes (m ∷ ms)
      ───────────────────────
      Σ[ p ∈ (te ∈ tes) ]
        FormedTE (tes ─ p) ms
  tc∉∈-FormedTE {ms = ms} {tes = tes} uniqTC ¬ftc ftc
    with ∃te ← L.All.¬All⇒Any¬ (_∙∈? ms) _ ¬ftc
    -- ∃te : Any (_∙∉ ms) tes
    with te , te∈ , te∉ ← satisfied′ ∃te
    -- te  : TimeoutEvidence
    -- te∈ : te ∈ tes
    -- te∉ : te ∙∉ ms
    with te∈∷@(mtc , m∈) ← L.All.lookup ftc te∈
    -- te∈∷ : te ∙∈ (m ∷ ms)
    -- mtc  : Maybe TC
    -- m∈   : Timeout (te , mtc) ∈ (m ∷ ms)
    with m∈
  ... | here refl
    -- te ≡ tm .proj₁
    = te∈ , L.All.tabulate QED
    where
    te∉─ : te ∉ (tes ─ te∈)
    te∉─ = ∉-─ node te∈ uniqTC

    QED : ∀ {te} → te ∈ (tes ─ te∈) → te ∙∈ ms
    QED {te} te∈─
      with L.All.lookup ftc {te} (∈-─⁻ _ te∈─)
    ... | mtc , there te∈ = mtc , te∈
    ... | mtc , here refl = ⊥-elim $ te∉─ te∈─
  ... | there te∈
    -- Timeout (te , mtc) ∈ ms
    = ⊥-elim $ te∉ (mtc , te∈)

  tc∉∈-FormedTC : let m = Timeout tm; te = tm .proj₁ in
    ∙ ¬ FormedTC tc ms
    ∙ FormedTC tc (m ∷ ms)
      ───────────────────────────
      Σ[ p ∈ (te ∈ tc .tes) ]
        FormedTE (tc .tes ─ p) ms
  tc∉∈-FormedTC {tc = tc} ¬ftc ftc = tc∉∈-FormedTE (getUniqueTC tc) ¬ftc ftc

  tc∉∈-Timeout : let m = Timeout tm; te = tm .proj₁ in
    ∙ tc ∙∉ ms
    ∙ tc ∙∈ (m ∷ ms)
      ───────────────────────────
      tc tc∈-Message m
    ⊎ Σ[ p ∈ (te ∈ tc .tes) ]
        FormedTE (tc .tes ─ p) ms
  tc∉∈-Timeout {tc = tc} tc∉ (formedTC ftc) =
    inj₂ $ tc∉∈-FormedTC {tc = tc} (tc∉ ∘ formedTC) ftc
  tc∉∈-Timeout tc∉ (receivedTC m∈) = case m∈ of λ where
    (here px)  → inj₁ px
    (there m∈) → ⊥-elim $ tc∉ $ receivedTC m∈
```
-->

### Highest QC

```agda
data _-highest-qc-∈-_ : QC → Messages → Type where
  isHighest :
    ∙ qc ∙∈ ms
    ∙ (∀ qc′ → qc′ ∙∈ ms → qc′ ≤qc qc)
      ────────────────────────────────
      qc -highest-qc-∈- ms
```

### Chain membership

The following predicate indicates that the chain has been "seen"
(i. e. it is in the database).

```agda
data _-chain-∈-_ : Chain → Messages → Type where
  [] :
    ────────────────────
    genesis -chain-∈- ms

  _∷_⊣_ :
    ∙ b ∙∈ ms
    ∙ ch -chain-∈- ms
    ∙ b -connects-to- ch
      ─────────────────────
      (b ∷ ch) -chain-∈- ms

-- TODO: refactor to this definition instead
-- _-chain-∈-_ : Chain → Messages → Type
-- ch -chain-∈- ms = All (_∙∈ ms) ch × ValidChain ch
```
<!--
```agda
instance Has∈-Chain = Has∈ Chain ∋ λ where ._∙∈_ → _-chain-∈-_

chain-∈⇒ValidChain :
  ch ∙∈ ms
  ─────────────
  ValidChain ch
chain-∈⇒ValidChain = λ where
  [] → []
  (_ ∷ ch∈ ⊣ b←) → _ ∷ chain-∈⇒ValidChain ch∈ ⊣ b←


chain-∈-mono : ch -chain-∈- ms → ch -chain-∈- (m ∷ ms)
chain-∈-mono [] = []
chain-∈-mono {ms = ms}{m} (b∈ ∷ ch∈ ⊣ b←) =
  ∈-allBlocks-there {ms = ms}{m} b∈ ∷ (chain-∈-mono ch∈) ⊣ b←

chain-∈-tail : (b ∷ ch) -chain-∈- ms → ch -chain-∈- ms
chain-∈-tail (_ ∷ ch∈ ⊣ _) = ch∈

chain-∉ : let b = sb .datum in
  ∙ b ∉ ch
  ∙ ch -chain-∈- (Propose sb ∷ ms)
    ──────────────────────────────
    ch -chain-∈- ms
chain-∉ pb∉ = λ where
 []                   → []
 (here refl ∷ _ ⊣ _)  → ⊥-elim (pb∉ $ here refl)
 (there b∈ ∷ ch∈ ⊣ x) → b∈ ∷ chain-∉ (pb∉ ∘ there) ch∈ ⊣ x

connects-to-> :
  ∙ b -connects-to- ch
  ∙ ch ∙∈ ms
    ────────────────────────────────────
    All (λ b′ → b ∙round > b′ ∙round) ch
connects-to-> bc [] = []
connects-to-> {b}{b₁ ∷ _} bc (b₁∈ ∷ ch∈ ⊣ b₁c) =
  b>b₁ ∷ b>tail
  where
  open Nat; open ≤-Reasoning

  b>b₁ : b ∙round > b₁ ∙round
  b>b₁ = begin
    suc (b₁ ∙round)          ≤⟨ s≤s $ ≤-reflexive $ sym $ bc .roundMatch ⟩
    suc (b .blockQC ∙round)  ≤⟨ bc .roundAdvances ⟩
    b ∙round                 ∎

  b>tail = L.All.map (flip ≤-trans $ <⇒≤ b>b₁)
         $ connects-to-> b₁c ch∈

chain-not-circular :
  ∙ b -connects-to- ch
  ∙ ch ∙∈ ms
    ────────
    b ∉ ch
chain-not-circular bc ch∈ b∈ =
  Nat.<-irrefl refl (L.All.lookup (connects-to-> bc ch∈) b∈)

getHighestQC : qc -highest-qc-∈- ms → ∀ qc′ → qc′ ∙∈ ms → qc′ ≤qc qc
getHighestQC (isHighest _ p) = p
```
-->

### Certified blocks

A block is certified if there exists a qc for that block.

```agda
data _-certified-∈-_ (b : Block) (ms : Messages) : Type where
  certified :
    -- ∙ b ∙∈ ms
    ∙ qc ∙∈ ms
    ∙ qc ∙blockId ≡ b ∙blockId
    ∙ qc ∙round   ≡ b ∙round
      ────────────────────────
      b -certified-∈- ms
```

### Final Chain

```agda
data _∶_final-∈_ : Block → Chain → Messages → Type where
  final∈ :
    ∙ b  -certified-∈- ms
    ∙ b′ -certified-∈- ms
    ∙ (b′ ∷ b ∷ ch) ∙∈ ms
    ∙ b′ ∙round ≡ 1 + b ∙round
      ────────────────────────
      b′ ∶ (b ∷ ch) final-∈ ms

_∶_longer-final-∈_ : Block → Chain → LocalState → Type
b ∶ ch longer-final-∈ ls
  = b ∶ ch final-∈ ls .db
  × length ch > length (ls .finalChain)

data _longer-final-∈_ : Block → LocalState → Type where
  mk : ∀ {ch} →
    (b ∶ ch longer-final-∈ ls)
    ──────────────────────────
    b longer-final-∈ ls
```

## Voting conditions
```agda
ShouldVote : LocalState → Block → Type
ShouldVote ls ⟨ qc , mtc , r , _ {-⊣ _-} ⟩
  = r ≡ ls .r-cur
  × r > ls .r-vote
  × ( {-(1)-} r ≡ 1 + qc ∙round
    ⊎ {-(2)-} Any (λ tc → r ≡ 1 + tc ∙round × qc ∙round ≥ highestQC tc ∙round) mtc
    )
```

## Proposal conditions
```agda
data _-connects-∈-_ (b : Block) (ms : Messages) : Type where
  mk : ∀ {ch : Chain} →
    ∙ ch -chain-∈- ms
    ∙ b -connects-to- ch
      ──────────────────
      b -connects-∈- ms

ValidProposal : Messages → Block → Type
ValidProposal ms b
  = AllBlock (λ b′ → b ∙round ≢ b′ ∙round) ms
  × b -connects-∈- ms -- this is also checked by Commit (longer-final-∈)


ValidProposal⇒ValidBlock : ValidProposal ms b → ValidBlock b
ValidProposal⇒ValidBlock (_ , mk _ (connects∶ _ _ vb)) = vb

```
