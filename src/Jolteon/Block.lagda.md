<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Block (⋯ : _) (open Assumptions ⋯) where

private variable
  a : Level
  A B : Type a

variable
  p p′ : Pid
  txn : List Transaction
```
-->

# Blocks

## Signatures on objects

### Signed Objects

We may sign hashable objects, such as votes, messages, etc.

```agda
record Signed (A : Type) : Type where
  constructor _signed-by_
  field datum     : A
        node      : Pid

  signature :  ⦃ _ : Digestable A ⦄ → Signature
  signature = sign (node ∙sk) datum

SignedShare = Signed
```
<!--
```agda
open Signed public

signData : ⦃ Digestable A ⦄ → Pid → A → Signed A
signData pid a = a signed-by pid

record HasPid (A : Type) : Type where
  field _∙pid : A → Pid
open HasPid ⦃...⦄ public

instance
  HasPid-Signed : HasPid (Signed A)
  HasPid-Signed ._∙pid = node

  DecEq-Signed : ⦃ DecEq A ⦄ → DecEq (Signed A)
  DecEq-Signed ._≟_ (d₁ signed-by p₁) (d₂ signed-by p₂) with d₁ ≟ d₂
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl with p₁ ≟ p₂
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl = yes refl
```
-->


###  Threshold signatures

```agda
BlockId = Hash

record ThresholdSig (A : Type) : Type where
  field payload       : A
        shares        : List Pid
        .uniqueShares : Unique shares
        .quorum       : IsMajority shares

-- If we follow the paper to the letter shares should be a list of (A × Pid)
-- such that all elements have payload as first component.
-- Morally a Share = Pid × A
```
<!--
```agda
open ThresholdSig public

variable idᵇ idᵇ′ : BlockId

module _ (ts : ThresholdSig A) (let record {quorum = q; uniqueShares = u} = ts) where
  getQuorum : IsMajority (ts .shares)
  getQuorum = recompute dec q

  getUnique : Unique (ts .shares)
  getUnique = recompute dec u
```
-->

## Quorum Certificates

```agda
QC = ThresholdSig (BlockId × Round)
     -- missing property: let (bid , r) = qc .payload.
     -- then ∀ b → blockId b ≡ bid → b ∙round ≡ r
     -- This condition was added to the connects-to predicate.

QCs = List QC
```
<!--
```agda
variable qc qc′ : QC
```
-->

How to digest a QC:
```agda
qcPayload : QC → PayloadQC
qcPayload qc = let bid , r = qc .payload in
  (bid , r , qc .shares)

qcPayload-inj : Injective≡ qcPayload
qcPayload-inj eq with refl , refl ← Prod.,-injective eq = refl

instance
  Digestable-QC : Digestable QC
  Digestable-QC = λ where
    .digest     → digest ∘ qcPayload
    .digest-inj → qcPayload-inj ∘ digest-inj

rqcPayload : Round × QC → ℕ × PayloadQC
rqcPayload = map₂ qcPayload

rqcPayload-inj : Injective≡ rqcPayload
rqcPayload-inj eq with refl , refl ← Prod.,-injective eq = refl

instance
  Digestable-ℕ×QC : Digestable (Round × QC)
  Digestable-ℕ×QC = λ where
    .digest     → digest ∘ rqcPayload
    .digest-inj → rqcPayload-inj ∘ digest-inj
```
<!--
```agda
record HasRound (A : Type) : Type where
  field _∙round : A → Round
open HasRound ⦃...⦄ public

instance
  HasRound-QC = HasRound QC ∋ λ where ._∙round → proj₂ ∘ payload

  HasRound-⊎ : ⦃ HasRound A ⦄ → ⦃ HasRound B ⦄ → HasRound (A ⊎ B)
  HasRound-⊎ ._∙round = λ where
    (inj₁ a) → a ∙round
    (inj₂ b) → b ∙round

  DecEq-QC : DecEq QC
  DecEq-QC ._≟_ qc qc′ with qc .payload ≟ qc′ .payload
  ... | no ¬eq   = no λ where refl → ¬eq refl
  ... | yes refl with qc .shares ≟ qc′ .shares
  ... | no ¬eq   = no λ where refl → ¬eq refl
  ... | yes refl = yes refl
```
-->

### QC order

Quorum certificates are ordered by round.

The following function returns the higher of two QCs.

<!--
```agda
_≤qc_ _<qc_ : Rel QC 0ℓ
_⊔qc_ : Op₂ QC
infix 4 _≤qc?_ _≤qc_ _<qc?_ _<qc_
```
-->
```agda
qc ≤qc qc′ = qc ∙round ≤ qc′ ∙round
qc <qc qc′ = qc ∙round < qc′ ∙round

_≤qc?_ = Decidable² _≤qc_ ∋ dec²
_<qc?_ = Decidable² _<qc_ ∋ dec²

qc ⊔qc qc′ = if ¿ qc ≤qc qc′ ¿ᵇ then qc′ else qc
```

### QC Property

In every qc there is an honest vote share.

```agda
qc⇒hp : ∀ (qc : QC) →
    ─────────────────────────────────
    ∃ λ p → p ∈ qc .shares × Honest p
qc⇒hp qc = satisfied′ $ honestFromMajority (getUnique qc) (getQuorum qc)
```

## Timeout Certificates

```agda
-- TimeoutEvidence comes from timeout messages
TimeoutEvidence = Signed (Round × QC)
```
<!--
```agda
instance
  HasRound-TE = HasRound TimeoutEvidence ∋ λ where ._∙round → proj₁ ∘ datum

_∙qcTE : TimeoutEvidence → QC
_∙qcTE = proj₂ ∘ datum
```
-->
```agda
record TC : Type where
  field
    roundTC : Round
    tes     : List TimeoutEvidence
    -- NB: should we only keep the highest QC?
    --     possibly a compressed TC' after gathering timeouts

    .quorumTC : IsMajority tes
    .uniqueTC : UniqueBy node tes
    -- ^ each piece of TimeoutEvidence should be signed by a different replica.
    .allRound : All (λ te → te ∙round       ≡ roundTC) tes
    .qcBound  : All (λ te → te ∙qcTE ∙round < roundTC) tes

TCs = List TC
```
<!--
```agda
open TC public

variable
  te te′ : TimeoutEvidence
  tc tc′ : TC
  mtc : Maybe TC

instance
  HasRound-TC = HasRound TC ∋ λ where ._∙round → roundTC

  DecEq-TC : DecEq TC
  DecEq-TC ._≟_ tc tc′
     with tc .roundTC ≟ tc′ .roundTC | tc .tes ≟ tc′ .tes
  ... | yes refl | yes refl = yes refl
  ... | no ¬eq   | _        = no λ where refl → ¬eq refl
  ... | yes _    | no ¬eq   = no λ where refl → ¬eq refl

module _ (tc : TC) (let record {quorumTC = q; uniqueTC = u; allRound = a; qcBound = b} = tc) where
  getQuorumTC : IsMajority (tc .tes)
  getQuorumTC = recompute dec q

  getUniqueTC : UniqueBy node (tc .tes)
  getUniqueTC = recompute dec u

  getAllRound : All (λ te → te ∙round ≡ tc .roundTC) (tc .tes)
  getAllRound = recompute dec a

  getQCBound  : All (λ te → te ∙qcTE ∙round < tc .roundTC) (tc .tes)
  getQCBound  = recompute dec b

qcsTES : List TimeoutEvidence → List QC
qcsTES = map _∙qcTE

qcsTES⁺ : (tes : List TimeoutEvidence) → IsMajority tes → List⁺ QC
qcsTES⁺ [] maj = ⊥-elim $ majority⁺ maj
qcsTES⁺ (te ∷ tes) _ = te ∙qcTE ∷ qcsTES tes

qcs⁺ : TC → List⁺ QC
qcs⁺ tc = qcsTES⁺ (tc .tes) (getQuorumTC tc)

qcs = L.NE.toList ∘ qcs⁺

qcs≡qcsTES : ∀ tc → qcs tc ≡ qcsTES (tc .tes)
qcs≡qcsTES tc@(record {tes = []}) = ⊥-elim $ majority⁺ (getQuorumTC tc)
qcs≡qcsTES (record {tes = _ ∷ _}) = refl

qcTE-lemma : te ∈ tes tc → te ∙qcTE ∈ qcs tc
qcTE-lemma (here refl) = here refl
qcTE-lemma (there te∈) = there $ L.Mem.∈-map⁺ _∙qcTE te∈
```
-->

How to digest a TC:
```agda
PayloadTE = Pid × PayloadQC

opaque
  tePayload : TimeoutEvidence → PayloadTE
  tePayload ((r , qc) signed-by p) = p , qcPayload qc

  tePayloads-inj : ∀ {tes tes′} →
    ∙ All (λ te → te ∙round ≡ r) tes
    ∙ All (λ te → te ∙round ≡ r) tes′
    ∙ map tePayload tes ≡ map tePayload tes′
      ──────────────────────────────────────
      tes ≡ tes′
  tePayloads-inj {tes = []}    []          []           refl = refl
  tePayloads-inj {tes = _ ∷ _} (refl ∷ r≡) (refl ∷ r≡′) tes≡
    with refl , tes≡ ← L.∷-injective tes≡
    = cong₂ _∷_ refl $ tePayloads-inj r≡ r≡′ tes≡

  tcPayload : TC → PayloadTC
  tcPayload tc = tc .roundTC , map tePayload (tc .tes)

  tcPayload-inj : Injective≡ tcPayload
  tcPayload-inj {tc}{tc′} tc≡
    with refl , tes≡ ← Prod.,-injective tc≡
    with refl ← tePayloads-inj (getAllRound tc) (getAllRound tc′) tes≡
    = refl

instance
  Digestable-TC : Digestable TC
  Digestable-TC = λ where
    .digest     → digest ∘ tcPayload
    .digest-inj → tcPayload-inj ∘ digest-inj
```

## Blocks

```agda
record Block : Type where
  constructor ⟨_,_,_,_⟩
  field
    blockQC : QC
    blockTC : Maybe TC
    round   : Round
    txs     : List Transaction

SBlock = Signed Block
```
<!--
```agda
open Block public

variable
  b b′ b″ : Block
  sb sb′ sb″ : SBlock

instance HasRound-Block = HasRound Block ∋ λ where ._∙round → round

opaque
  blockPayload : Block → PayloadBlock
  blockPayload ⟨ qc , tc? , r , txs ⟩ = qcPayload qc , M.map tcPayload tc? , r , txs

  blockPayload-inj : Injective≡ blockPayload
  blockPayload-inj {b}{b′} b≡
    with refl , b≡   ← Prod.,-injective b≡
    with tc≡  , b≡   ← Prod.,-injective b≡
    with refl , refl ← Prod.,-injective b≡
    = cong (λ ◆ → ⟨ _ , ◆ , _ , _ ⟩)
    $ M.map-injective tcPayload-inj tc≡

instance
  Digestable-Block : Digestable Block
  Digestable-Block = λ where
    .digest     → digest ∘ blockPayload
    .digest-inj → blockPayload-inj ∘ digest-inj

record HasBlockId (A : Type) : Type where
  field _∙blockId : A → BlockId
open HasBlockId ⦃...⦄ public
record HasTC (A : Type) : Type where
  field _∙tc : A → TC
open HasTC ⦃...⦄ public
record HasTC? (A : Type) : Type where
  field _∙tc? : A → Maybe TC
open HasTC? ⦃...⦄ public
record HasQC (A : Type) : Type where
  field _∙qc : A → QC
open HasQC ⦃...⦄ public

instance
  HasBlockId-Block = HasBlockId Block ∋ λ where ._∙blockId → _♯
  HasBlockId-QC    = HasBlockId QC    ∋ λ where ._∙blockId → proj₁ ∘ payload

  HasQC-Block  = HasQC  Block ∋ λ where ._∙qc  → blockQC
  HasTC?-Block = HasTC? Block ∋ λ where ._∙tc? → blockTC

  HasQC-SBlock  = HasQC  SBlock ∋ λ where ._∙qc  → _∙qc  ∘ datum
  HasTC?-SBlock = HasTC? SBlock ∋ λ where ._∙tc? → _∙tc? ∘ datum
```
-->

## Genesis and Genesis QC

```agda
Chain = List Block

genesis : Chain
genesis = []
```
<!--
```agda
opaque
  chainPayload : Chain → PayloadChain
  chainPayload = map blockPayload

  chainPayload-inj : Injective≡ chainPayload
  chainPayload-inj = L.map-injective blockPayload-inj

instance
  Digestable-Chain : Digestable Chain
  Digestable-Chain = λ where
    .digest     → digest ∘ chainPayload
    .digest-inj → chainPayload-inj ∘ digest-inj
```
-->
```agda
genesisId = genesis ♯

qc₀ : QC
qc₀ = record
  { payload      = genesisId , 0
  ; shares       = allPids
  ; uniqueShares = L.Unique.tabulate⁺ {f = id} id
  ; quorum       = allPidsMajority
  }

instance
  HasBlockId-Chain = HasBlockId Chain ∋ λ where
    ._∙blockId []      → genesisId
    ._∙blockId (b ∷ _) → b ∙blockId
  HasRound-Chain = HasRound Chain ∋ λ where
    ._∙round []      → 0
    ._∙round (b ∷ _) → b ∙round
```
<!--
```agda
variable ch ch′ : Chain

-- TODO: generalize Has∈ (Prelude.Membership) and use that instead
_∈₁_ : ∀{A : Type} → A → List⁺ A → Type
x ∈₁ xs = x ∈ (L.NE.toList xs)

private
  maxNE′ : QC → QCs → QC
  maxNE′ q [] = q
  maxNE′ q (x ∷ xs) = q ⊔qc maxNE′ x xs

  q≤q⊔q′ : ∀ {q qˡ qʳ} → q ≤qc qˡ → q ≤qc qˡ ⊔qc qʳ
  q≤q⊔q′ {q}{qˡ}{qʳ} ≤l
    with ¿ qˡ ≤qc qʳ ¿
  ... | yes l≤ = Nat.≤-trans ≤l l≤
  ... | no  _  = ≤l

  q≤q′⊔q : ∀ {q qˡ qʳ} → q ≤qc qʳ → q ≤qc qˡ ⊔qc qʳ
  q≤q′⊔q {q}{qˡ}{qʳ} ≤r
    with ¿ qˡ ≤qc qʳ ¿
  ... | yes _  = ≤r
  ... | no  l< = Nat.≤-trans ≤r (Nat.≰⇒≥ l<)

  maxNE′-≤ : ∀ {q} {qs} → q ≤qc maxNE′ q qs
  maxNE′-≤ {q} {[]}    = Nat.≤-refl
  maxNE′-≤ {q} {_ ∷ _} = q≤q⊔q′ {q = q} Nat.≤-refl

  maxNE′-correct : ∀ {q q′} {qs} → q .payload ∈ map payload qs → q ≤qc maxNE′ q′ qs
  maxNE′-correct {q} {q′} {_ ∷ qs} (here refl) =
    q≤q′⊔q {q}{q′} (maxNE′-≤ {qs = qs})
  maxNE′-correct {q} {q′} {_ ∷ qs} (there q∈) =
    q≤q′⊔q {q}{q′} (maxNE′-correct {q = q} q∈)

  maxNE′-correct′ : ∀ {q q′} {qs} → q ∈ qs → q ≤qc maxNE′ q′ qs
  maxNE′-correct′ {q} = maxNE′-correct {q} ∘ L.Mem.∈-map⁺ payload

maxNE : List⁺ QC → QC
maxNE (q ∷ qs) = maxNE′ q qs

module _ {q} where
  maxNE-correct : ∀ {qs} → payload q ∈₁ L.NE.map payload qs → q ≤qc maxNE qs
  maxNE-correct {[ q′ ]}     (here refl) = Nat.≤-refl
  maxNE-correct {q′ ∷ _ ∷ _} (here refl) = q≤q⊔q′ {q = q} Nat.≤-refl
  maxNE-correct {_ ∷ _}      (there q∈)  = maxNE′-correct {q = q} q∈

  maxNE-correct′ : ∀ {qs} → q ∈₁ qs → q ≤qc maxNE qs
  maxNE-correct′ = maxNE-correct ∘ L.Mem.∈-map⁺ payload
```
-->
```agda
highestQC : TC → QC
highestQC tc = maxNE (qcs⁺ tc)
```
<!--
```agda
highestQC∈List : (q : QC) (qs : QCs) → maxNE (q ∷ qs) ∈₁ (q ∷ qs)
highestQC∈List x [] = here refl
highestQC∈List x (y ∷ ys) with ¿ x ≤qc maxNE′ y ys ¿ᵇ
... | true  = there (highestQC∈List y ys)
... | false = here refl

highestQC∈TC : ∀ (tc : TC) → highestQC tc ∈₁ (qcs⁺ tc)
highestQC∈TC tc with q ∷ qs ← qcs⁺ tc = highestQC∈List q qs

highestQC-correct : {q : QC}(tc : TC) → q ∈ (qcs tc) → q ≤qc highestQC tc
highestQC-correct tc = maxNE-correct′

instance
  DecEq-Block : DecEq Block
  DecEq-Block ._≟_ ⟨ qc , mtc , r , txs {-⊣ _-} ⟩ ⟨ qc′ , mtc′ , r′ , txs′ {-⊣ _-} ⟩
    with qc ≟ qc′
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl with mtc ≟ mtc′
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl with r ≟ r′
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl with txs ≟ txs′
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl = yes refl
```
-->

###

```agda
ValidBlock : Block → Type
ValidBlock b = b ∙round > b .blockQC ∙round

record _-connects-to-_ (b : Block) (ch : Chain) : Type where
  constructor connects∶
  field idMatch       : (b .blockQC) ∙blockId ≡ ch ∙blockId
        roundMatch    : (b .blockQC) ∙round   ≡ ch ∙round
        roundAdvances : ValidBlock b -- TODO: move to Block
open _-connects-to-_ public
```
<!--
```agda
ValidBlock⇒round⁺ :
  ValidBlock b
  ────────────
  b ∙round ≢ 0
ValidBlock⇒round⁺ () refl

data ValidChain : Chain → Type where
  [] :
    ──────────────────
    ValidChain genesis

  _∷_⊣_ : ∀ b →
    ∙ ValidChain ch
    ∙ b -connects-to- ch
      ───────────────────
      ValidChain (b ∷ ch)

uniqueChain :
 ∙ ValidChain ch
 ∙ ValidChain ch′
 ∙ ch ∙blockId ≡ ch′ ∙blockId
   ──────────────────────────
   ch ≡ ch′
uniqueChain [] [] id≡ = refl
uniqueChain [] (b ∷ vch′ ⊣ x) id≡ = ⊥-elim $ noHashCollision id≡
uniqueChain (b ∷ vch ⊣ x) [] id≡ =  ⊥-elim $ noHashCollision˘ id≡
uniqueChain (b ∷ vch ⊣ bc) (b′ ∷ vch′ ⊣ bc′) id≡
  with connects∶ qc≡ _ _  ← bc
  with connects∶ qc≡′ _ _ ← bc′
  with b≡ ← ♯-inj {x = b}{b′} id≡
  rewrite b≡
  = cong (_ ∷_) $ uniqueChain vch vch′ (trans (sym qc≡) qc≡′)
```
-->
