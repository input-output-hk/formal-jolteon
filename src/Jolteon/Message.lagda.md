## Messages

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Message (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
```
-->


## Messages

```agda
-- r-cur, current QC_high , when QC-high.r = r-cur - 1 then TC = nothing else TC.r = r-1
TimeoutMessage = TimeoutEvidence × Maybe TC
Proposal       = Signed Block
VoteShare      = SignedShare (BlockId × Round)
TCMessage      = {- Signed -} TC

instance
  HasRound-VS = HasRound VoteShare      ∋ λ where ._∙round →  proj₂  ∘ datum
  HasRound-TM = HasRound TimeoutMessage ∋ λ where ._∙round → _∙round ∘ proj₁

  HasBlockId-VS = HasBlockId VoteShare ∋ λ where ._∙blockId → proj₁ ∘ datum

data Message : Type where
  Propose  : Proposal       → Message
  Vote     : VoteShare      → Message
  TCFormed : TCMessage      → Message
  Timeout  : TimeoutMessage → Message

Messages   = List Message
VoteShares = List VoteShare
```
<!--
```agda
variable
  vs vs′ : VoteShare
  vss vss′ : VoteShares

instance
  DecEq-Message : DecEq Message
  DecEq-Message ._≟_ (Propose x)  (Propose y) with x ≟ y
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl = yes refl
  DecEq-Message ._≟_ (Propose _)  (Vote _)     = no λ where ()
  DecEq-Message ._≟_ (Propose _)  (TCFormed _) = no λ where ()
  DecEq-Message ._≟_ (Propose _)  (Timeout _)  = no λ where ()
  DecEq-Message ._≟_ (Vote _)     (Propose _)  = no λ where ()
  DecEq-Message ._≟_ (Vote x)     (Vote y) with x ≟ y
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl = yes refl
  DecEq-Message ._≟_ (Vote _)     (TCFormed _) = no λ where ()
  DecEq-Message ._≟_ (Vote _)     (Timeout _)  = no λ where ()
  DecEq-Message ._≟_ (TCFormed _) (Propose _)  = no λ where ()
  DecEq-Message ._≟_ (TCFormed _) (Vote _)     = no λ where ()
  DecEq-Message ._≟_ (TCFormed x) (TCFormed y) with x ≟ y
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl = yes refl
  DecEq-Message ._≟_ (TCFormed _) (Timeout _)  = no λ where ()
  DecEq-Message ._≟_ (Timeout _)  (Propose _)  = no λ where ()
  DecEq-Message ._≟_ (Timeout _)  (Vote _)     = no λ where ()
  DecEq-Message ._≟_ (Timeout _)  (TCFormed _) = no λ where ()
  DecEq-Message ._≟_ (Timeout x)  (Timeout y)  with x ≟ y
  ... | no ¬eq = no λ where refl → ¬eq refl
  ... | yes refl = yes refl

variable
  m m′ : Message
  ms ms′ : Messages
  mm : Maybe Message
  tm : TimeoutMessage

¬Vote : Message → Type
¬Vote = λ where
  (Vote _) → ⊥
  _        → ⊤

¬Timeout : Message → Type
¬Timeout = λ where
  (Timeout _)  → ⊥
  _            → ⊤

messageBlock : Message → Maybe SBlock
messageBlock = λ where
  (Propose sb) → just sb
  _            → nothing

allSBlocks : Messages → List SBlock
allSBlocks = L.mapMaybe messageBlock

allBlocks : Messages → List Block
allBlocks = map datum ∘ allSBlocks

⊆-allSBlocks⁺ :
  ms ⊆ˢ ms′
  ───────────────────────────────
  allSBlocks ms ⊆ˢ allSBlocks ms′
⊆-allSBlocks⁺ = mapMaybe-⊆ messageBlock

⊆-allBlocks⁺ :
  ms ⊆ˢ ms′
  ─────────────────────────────
  allBlocks ms ⊆ˢ allBlocks ms′
⊆-allBlocks⁺ = L.SubS.map⁺ datum ∘ ⊆-allSBlocks⁺

∈-allSBlocks⁺ˡ :
  sb ∈ allSBlocks ms
  ───────────────────────────
  sb ∈ allSBlocks (ms ++ ms′)
∈-allSBlocks⁺ˡ {ms = ms} = ∈-mapMaybe-++⁺ˡ messageBlock {ms}

∈-allSBlocks⁺ʳ :
  sb ∈ allSBlocks ms′
  ───────────────────────────
  sb ∈ allSBlocks (ms ++ ms′)
∈-allSBlocks⁺ʳ {ms = ms} = ∈-mapMaybe-++⁺ʳ messageBlock ms

∈-allSBlocks⁻ :
  sb ∈ allSBlocks ms
  ──────────────────
  Propose sb ∈ ms
∈-allSBlocks⁻ {ms = m ∷ ms} sb∈
  with m | sb∈
... | Propose sb | here refl = here refl
... | Propose _  | there sb∈ = there $′ ∈-allSBlocks⁻ sb∈
... | Vote _     | sb∈ = there $′ ∈-allSBlocks⁻ sb∈
... | TCFormed _ | sb∈ = there $′ ∈-allSBlocks⁻ sb∈
... | Timeout _  | sb∈ = there $′ ∈-allSBlocks⁻ sb∈

∈-allBlocks⁺ˡ :
  b ∈ allBlocks ms
  ─────────────────────────
  b ∈ allBlocks (ms ++ ms′)
∈-allBlocks⁺ˡ {ms = ms} b∈
  with sb , sb∈ , refl ← L.Mem.∈-map⁻ datum b∈
  = L.Mem.∈-map⁺ datum $ ∈-allSBlocks⁺ˡ {ms = ms} sb∈

∈-allBlocks⁺ʳ :
  b ∈ allBlocks ms′
  ─────────────────────────
  b ∈ allBlocks (ms ++ ms′)
∈-allBlocks⁺ʳ {ms = ms} b∈
  with sb , sb∈ , refl ← L.Mem.∈-map⁻ datum b∈
  = L.Mem.∈-map⁺ datum $ ∈-allSBlocks⁺ʳ {ms = ms} sb∈

∈-allBlocks-there :
  b ∈ allBlocks ms
  ──────────────────────
  b ∈ allBlocks (m ∷ ms)
∈-allBlocks-there {ms = ms} {m = m} = ∈-allBlocks⁺ʳ {ms′ = ms} {ms = [ m ]}

∈-allBlocks⁻ :
  b ∈ allBlocks ms
  ──────────────────
  ∃ λ (sb : SBlock)
    → sb ∈ allSBlocks ms
    × b ≡ sb .datum
∈-allBlocks⁻ = L.Mem.∈-map⁻ datum

```
-->
```agda
data _qc∈-Message_ (qc : QC) : Message → Type where
  qc∈-Propose :
    qc ≡ sb ∙qc
    ─────────────────────────
    qc qc∈-Message Propose sb

  qc∈-ProposeTC :
    ∙ sb ∙tc? ≡ just tc
    ∙ qc ∈₁ qcs⁺ tc
      ─────────────────────────
      qc qc∈-Message Propose sb

  qc∈-TCFormed :
    qc ∈₁ qcs⁺ tc
    ──────────────────────────
    qc qc∈-Message TCFormed tc

  qc∈-Timeout : ∀{tm} →
    qc ≡ (tm .proj₁) ∙qcTE
    ─────────────────────────
    qc qc∈-Message Timeout tm

  qc∈-TimeoutTC : ∀{tm} →
    ∙ tm .proj₂ ≡ just tc
    ∙ qc ∈₁ qcs⁺ tc
      ─────────────────────────
      qc qc∈-Message Timeout tm

data _tc∈-Message_ (tc : TC) : Message → Type where
  tc∈-Propose :
    sb ∙tc? ≡ just tc
    ─────────────────────────
    tc tc∈-Message Propose sb

  tc∈-TCFormed :
    ──────────────────────────
    tc tc∈-Message TCFormed tc

  tc∈-Timeout : ∀{tm} →
    tm .proj₂ ≡ just tc
    ─────────────────────────
    tc tc∈-Message Timeout tm
```

```agda
IsTimeoutForRound : Round → Message → Type
IsTimeoutForRound r (Timeout (te , _)) = te ∙round ≡ r
IsTimeoutForRound r _ = ⊥

VotesFor : Block → Message → Type
VotesFor b = λ where
  (Vote vs) → vs ∙blockId ≡ b ∙blockId
  _ → ⊥
```
<!--
```agda
-- VotesFor' : Pid → Block → Message → Type
-- VotesFor' p b = λ where
--   (Vote vs) → (vs ∙pid ≡ p) × (vs ∙blockId ≡ b ∙blockId)
--   _ → ⊥

IsTimeoutForRound? : Decidable² IsTimeoutForRound
IsTimeoutForRound? r = λ where
  (Propose _)        → no λ ()
  (Vote _)           → no λ ()
  (TCFormed _)       → no λ ()
  (Timeout (te , _)) → (te ∙round) ≟ r

VotesFor? : Decidable² VotesFor
VotesFor? b = λ where
  (Vote vs)    → (vs ∙blockId) ≟ (b ∙blockId)
  (Propose _)  → no λ ()
  (TCFormed _) → no λ ()
  (Timeout _)  → no λ ()

-- VotesFor'? : ∀ p b m → Dec (VotesFor' p b m)
-- VotesFor'? p b = λ where
--   (Vote vs)    → (((vs ∙blockId) ≟ (b ∙blockId)) ×-dec ((vs ∙pid) ≟ p))
--   (Propose _)  → no λ ()
--   (TCFormed _) → no λ ()
--   (Timeout _)  → no λ ()

_∙sender? : Message → Maybe Pid
_∙sender? = λ where
  (Propose pr)       → just (pr ∙pid)
  (Vote vs)          → just (vs ∙pid)
  (TCFormed _)       → nothing
  (Timeout (te , _)) → just (te ∙pid)
```
-->


## Envelopes

Envelopes add a recipient to a message `(recipient = just p)`, or are
a broadcast message (`recipient = nothing`).

```agda
record Envelope : Type where
   constructor [_?∣_⟩
   field recipient : Maybe Pid
         content   : Message
```
<!--
```agda
pattern [_∣_⟩ p m = [ just p  ?∣ m ⟩
pattern [_⟩     m = [ nothing ?∣ m ⟩
open Envelope public

variable
  env env′ : Envelope
  envs envs′ : List Envelope
  menv menv′ : Maybe Envelope

record HasMessage (A : Type) : Type where
  field _∙message : A → Message
  infix 100 _∙message
open HasMessage ⦃...⦄ public

instance
  HasMsg-Env = HasMessage Envelope ∋ λ where ._∙message → content

  DecEq-Envelope : DecEq Envelope
  DecEq-Envelope ._≟_ [ p ?∣ m ⟩ [ p′ ?∣ m′ ⟩
    with p ≟ p′ | m ≟ m′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
```
-->
