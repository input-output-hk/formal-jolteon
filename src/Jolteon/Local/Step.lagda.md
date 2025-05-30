
# Transitions between local states of a single node.

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Local.Step (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
open import Jolteon.Message ⋯
open import Jolteon.Local.State ⋯
```
-->

## Some auxiliary functions

```agda
enterRound : Time → Op₁ LocalState
enterRound currentTime ls = record ls
  { timer          = just (currentTime + τ)
  ; phase          = Proposing
  ; roundAdvanced? = false
  }

propose : Op₁ LocalState
propose ls = record ls
  { phase = Receiving }

recordTimeout : Op₁ LocalState
recordTimeout ls = record ls
  { timer     = nothing -- don't fire again.
  ; timedOut? = true
  ; r-vote    = 1 + ls .r-cur
  }

registerMessage : (ls : LocalState) → m ∈ ls .inbox → LocalState
registerMessage {m} ls m∈ = record ls
  { phase = AdvancingRound
  ; db    = m ∷ ls .db
  ; inbox = L.removeAt (ls .inbox) (L.Any.index m∈)
  }

registerTimeout  = registerMessage
registerVote     = registerMessage
registerProposal = registerMessage

advanceRound : QC ⊎ TC → Op₁ LocalState
advanceRound qtc ls = record ls
  { phase          = AdvancingRound
  ; r-cur          = 1 + qtc ∙round
  ; tc-last        = Sum.isInj₂ qtc
  ; timer          = nothing
  ; timedOut?      = false
  ; roundAdvanced? = true
  }

lock : QC → Op₁ LocalState
lock qc ls = record ls
  { qc-high = qc  -- ⊔qc ls .qc-high
  ; phase   = Committing
  }

commit : Chain → Op₁ LocalState
commit ch ls =  record ls
  { phase      = Voting
  ; finalChain = ch
  }

shouldEnterRound : Op₁ LocalState
shouldEnterRound ls = record ls
  { phase = if ls .roundAdvanced? then EnteringRound else Receiving }

voteProposal : Op₁ LocalState
voteProposal ls = record (shouldEnterRound ls)
  { r-vote = ls .r-cur }
```

## The local step relation

Given a local state a step may produce a list of messages.

```agda
data _⦂_⊢_—_—→_ p t ls : Maybe Envelope → LocalState → Type

-- special case of step sending one message to one recipient
_⦂_⊢_—[_∣_⟩—→_ : Pid → Time → LocalState → Pid → Message → LocalState → Type
p ⦂ t ⊢ ls —[ p′ ∣ m ⟩—→ ls′ = p ⦂ t ⊢ ls — just [ p′ ∣ m ⟩ —→ ls′

-- special case of step multicasting one message
_⦂_⊢_—[_]—→_ : Pid → Time → LocalState → Message → LocalState → Type
p ⦂ t ⊢ ls —[ m ]—→ ls′ = p ⦂ t ⊢ ls — just [ m ⟩ —→ ls′

-- special case of step sending no message
_⦂_⊢_——→_ : Pid → Time → LocalState → LocalState → Type
p ⦂ t ⊢ ls ——→ ls′ = p ⦂ t ⊢ ls — nothing —→ ls′

data _⦂_⊢_—_—→_ p t ls where

  --------------------------
  -- * EnteringRound
  --------------------------

  -- Initialisation: replica enters round either with a TC or without one
  InitTC : let L = currentLeader ls; m = TCFormed tc in
    ∙ ls .phase ≡ EnteringRound
    ∙ ls .tc-last ≡ just tc
      ───────────────────────────────────────
      p ⦂ t ⊢ ls —[ L ∣ m ⟩—→ enterRound t ls

  InitNoTC :
    ∙ ls .phase ≡ EnteringRound
    ∙ ls .tc-last ≡ nothing
      ──────────────────────────────
      p ⦂ t ⊢ ls ——→ enterRound t ls

  --------------------------
  -- * Proposing
  --------------------------

  -- Leader proposes a new block.
  ProposeBlock :
    let
      L  = currentLeader ls
      b  = mkBlockForState ls txn
      m  = Propose $ signData L b
    in
    ∙ ls .phase ≡ Proposing
    ∙ p ≡ L
      ──────────────────────────────
      p ⦂ t ⊢ ls —[ m ]—→ propose ls

  -- Non-leader skips proposing.
  ProposeBlockNoOp : let L = currentLeader ls in
    ∙ ls .phase ≡ Proposing
    ∙ p ≢ L
      ─────────────────────────
      p ⦂ t ⊢ ls ——→ propose ls

  --------------------------
  -- * Receiving
  --------------------------

  RegisterProposal :
    let
      m = Propose sb
      b = sb .datum
    in
    ∀ (m∈ : m ∈ ls .inbox) →
    ∙ ls .phase ≡ Receiving
    ∙ ¬ timedOut ls t
    ∙ sb .node ≡ roundLeader (b ∙round)
    ∙ ValidProposal (ls .db) b
      ─────────────────────────────────────
      p ⦂ t ⊢ ls ——→ registerProposal ls m∈

  RegisterVote :
    let
      L′ = roundLeader (1 + r)
      m  = Vote $ signData p′ (b ∙blockId , r)
    in
    ∀ (m∈ : m ∈ ls .inbox) →
    ∙ ls .phase ≡ Receiving
    ∙ ¬ timedOut ls t
    ∙ b ∙∈ ls .db
    ∙ m ∉ ls .db
    ∙ L′ ≡ p
      ─────────────────────────────────
      p ⦂ t ⊢ ls ——→ registerVote ls m∈

  RegisterTimeout : let m = Timeout tm in
    ∀ (m∈ : m ∈ ls .inbox) →
    ∙ ls .phase ≡ Receiving
    ∙ ¬ timedOut ls t
    ∙ m ∉ ls .db
      ────────────────────────────────────
      p ⦂ t ⊢ ls ——→ registerTimeout ls m∈

  RegisterTC : let m = TCFormed tc in
    ∀ (m∈ : m ∈ ls .inbox) →
    ∙ ls .phase ≡ Receiving
    ∙ ¬ timedOut ls t
    ∙ m ∉ ls .db
      ────────────────────────────────────
      p ⦂ t ⊢ ls ——→ registerTimeout ls m∈

  EnoughTimeouts :
    let
      m   = Timeout $ signData p (ls .r-cur , ls .qc-high) , ls .tc-last
      tms = filter (IsTimeoutForRound? r) (ls .db)
    in
    ∙ ls .phase ≡ Receiving
    ∙ ¬ timedOut ls t
    ∙ IncludesHonest tms
    ∙ r ≥ ls .r-cur
      ────────────────────────────────────
      p ⦂ t ⊢ ls —[ m ]—→ recordTimeout ls

  TimerExpired :
    let m = Timeout $ signData p (ls .r-cur , ls .qc-high) , ls .tc-last in
    ∙ ls .phase ≡ Receiving
    ∙ timedOut ls t
      ────────────────────────────────────
      p ⦂ t ⊢ ls —[ m ]—→ recordTimeout ls

  --------------------------
  -- * AdvancingRound
  --------------------------

  AdvanceRoundQC :
    ∙ ls .phase ≡ AdvancingRound
    ∙ qc ∙∈ ls .db
    ∙ qc ∙round ≥ ls .r-cur
      ──────────────────────────────────────────
      p ⦂ t ⊢ ls ——→ advanceRound (inj₁ qc) ls

  AdvanceRoundTC :
    ∙ ls .phase ≡ AdvancingRound
    ∙ tc ∙∈ ls .db
    ∙ tc ∙round ≥ ls .r-cur
      ──────────────────────────────────────────
      p ⦂ t ⊢ ls ——→ advanceRound (inj₂ tc) ls

  AdvanceRoundNoOp : --when no new QC or TC has formed yet.
    ∙ ls .phase ≡ AdvancingRound
    ∙ AllQC (λ qc → qc ∙round < ls .r-cur) (ls .db)
    ∙ AllTC (λ tc → tc ∙round < ls .r-cur) (ls .db)
      ─────────────────────────────────────────────
      p ⦂ t ⊢ ls ——→ record ls { phase = Locking }

  --------------------------
  -- * Locking
  --------------------------

  Lock :
    ∙ ls .phase ≡ Locking
    ∙ qc -highest-qc-∈- ls .db
      ─────────────────────────
      p ⦂ t ⊢ ls ——→ lock qc ls

  --------------------------
  -- * Committing
  --------------------------

  Commit :
    ∙ ls .phase ≡ Committing
    ∙ b ∶ ch longer-final-∈ ls
      ───────────────────────────
      p ⦂ t ⊢ ls ——→ commit ch ls

  CommitNoOp :
    ∙ ls .phase ≡ Committing
    ∙ NoBlock (_longer-final-∈ ls) (ls .db)
      ─────────────────────────────────────────
      p ⦂ t ⊢ ls ——→ record ls {phase = Voting}

  --------------------------
  -- * Voting
  --------------------------

  VoteBlock :
    let
      m  = Vote $ signData p (b ∙blockId , b ∙round)
      L′ = nextLeader ls
    in
    ∙ ls .phase ≡ Voting
    ∙ b ∙∈ ls .db
    ∙ ShouldVote ls b
      ────────────────────────────────────────
      p ⦂ t ⊢ ls —[ L′ ∣ m ⟩—→ voteProposal ls

  VoteBlockNoOp :
    ∙ ls .phase ≡ Voting
    ∙ NoBlock (ShouldVote ls) (ls .db)
      ──────────────────────────────────
      p ⦂ t ⊢ ls ——→ shouldEnterRound ls
```

A node can also receive messages at their inbox:

```agda
receiveMessage : Message → Op₁ LocalState
receiveMessage m ls = record ls
  { inbox = ls .inbox L.∷ʳ m }
```
