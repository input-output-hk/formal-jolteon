<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Decidability.SmartConstructors
  (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Decidability.HighestQC ⋯
open import Jolteon.Decidability.AllTCs ⋯
open import Jolteon.Decidability.Final ⋯
```
-->

## Smart Constructors

We can now provide smart constructors for using proof-by-reflection
without calling `auto`:

```agda
mkQC : ∀ (b : Block) pids
  → {_ : auto∶ Unique pids}
  → {_ : auto∶ IsMajority pids}
  → QC
mkQC b sh {x} {y} = record
  { payload      = b ∙blockId , b ∙round
  ; shares       = sh
  ; uniqueShares = toWitness x
  ; quorum       = toWitness y
  }

mkTC : ∀ (roundTC : Round) (tes : List TimeoutEvidence)
  → {_ : auto∶ IsMajority tes}
  → {_ : auto∶ Unique (map node tes)}
  → {_ : auto∶ All (λ te → te ∙round ≡ roundTC) tes}
  → {_ : auto∶ All (λ te → te ∙qcTE ∙round < roundTC) tes}
  → TC
mkTC r tes {x} {y} {z} {w} = record
  { roundTC  = r
  ; tes      = tes
  ; quorumTC = toWitness x
  ; uniqueTC = toWitness y
  ; allRound = toWitness z
  ; qcBound  = toWitness w
  }

module _ {ls : LocalState} (let L = currentLeader ls) p where
  ≪InitTC? :
    {h : auto∶ ls .phase ≡ EnteringRound}
    {_ : auto∶ ls .tc-last ≡ just tc}
    → p ⦂ t ⊢ ls — _ —→ _
  ≪InitTC? {h = x}{y} = InitTC (toWitness x) (toWitness y)

  ≪InitNoTC? :
    {h : auto∶ ls .phase ≡ EnteringRound}
    {_ : auto∶ ls .tc-last ≡ nothing}
    → p ⦂ t ⊢ ls — _ —→ _
  ≪InitNoTC? {h = x}{y} = InitNoTC (toWitness x) (toWitness y)

  ≪ProposeBlock? : ∀ txn →
    let
      b   = mkBlockForState ls txn
      m   = Propose $ signData L b
    in
    {_ : auto∶ ls .phase ≡ Proposing}
    {_ : auto∶ p ≡ L}
    → p ⦂ t ⊢ ls —[ m ]—→ propose ls
  ≪ProposeBlock? _ {x}{y} = ProposeBlock (toWitness x) (toWitness y)

  ≪ProposeBlockNoOp? :
    {h : auto∶ ls .phase ≡ Proposing}
    {_ : auto∶ p ≢ L}
    → p ⦂ t ⊢ ls ——→ propose ls
  ≪ProposeBlockNoOp? {h = x}{y} = ProposeBlockNoOp (toWitness x) (toWitness y)

  ≪RegisterProposal? : let m = Propose sb; b = sb .datum in
    {m∈ : auto∶ m ∈ ls .inbox}
    {_  : auto∶ ls .phase ≡ Receiving}
    {_  : auto∶ ¬ timedOut ls t}
    {_  : auto∶ sb .node ≡ roundLeader (b ∙round)}
    {_  : auto∶ ValidProposal (ls .db) b}
    → p ⦂ t ⊢ ls ——→ registerProposal ls (toWitness m∈)
  ≪RegisterProposal? {m∈ = x}{y}{z}{w}{q} = RegisterProposal
    (toWitness x) (toWitness y) (toWitness z) (toWitness w) (toWitness q)

  ≪RegisterVote? : ∀ (b : Block) p′ →
    let
      L′ = roundLeader (1 + r)
      m  = Vote $ signData p′ (b ∙blockId , r)
    in
    {m∈ : auto∶ m ∈ ls .inbox}
    {_  : auto∶ ls .phase ≡ Receiving}
    {_  : auto∶ ¬ timedOut ls t}
    {_  : auto∶ b ∙∈ ls .db}
    {_  : auto∶ m ∉ ls .db}
    {_  : auto∶ L′ ≡ p}
    → p ⦂ t ⊢ ls ——→ registerVote ls (toWitness m∈)
  ≪RegisterVote? _ _ {x}{y}{z}{w}{q}{k} =
    RegisterVote (toWitness x) (toWitness y) (toWitness z) (toWitness w)
                 (toWitness q) (toWitness k)

  ≪RegisterTimeout? : ∀ tm → let m = Timeout tm in
    {m∈ : auto∶ m ∈ ls .inbox}
    {_ : auto∶ ls .phase ≡ Receiving}
    {_ : auto∶ ¬ timedOut ls t}
    {_ : auto∶ m ∉ ls .db}
    → p ⦂ t ⊢ ls ——→ registerTimeout ls (toWitness m∈)
  ≪RegisterTimeout? _ {x}{y}{z}{w} =
    RegisterTimeout (toWitness x) (toWitness y) (toWitness z) (toWitness w)

  ≪RegisterTC? : let m = TCFormed tc in
    {m∈ : auto∶ m ∈ ls .inbox}
    {_ : auto∶ ls .phase ≡ Receiving}
    {_ : auto∶ ¬ timedOut ls t}
    {_  : auto∶ m  ∉ ls .db}
    → p ⦂ t ⊢ ls ——→ registerTimeout ls (toWitness m∈)
  ≪RegisterTC? {m∈ = x}{y}{z}{w} =
    RegisterTC (toWitness x) (toWitness y) (toWitness z) (toWitness w)

  ≪EnoughTimeouts? : ∀ r →
    let
      m   = Timeout $ signData p (ls .r-cur , ls .qc-high) , ls .tc-last
      tms = filter (IsTimeoutForRound? r) (ls .db)
    in
    {_ : auto∶ ls .phase ≡ Receiving}
    {_ : auto∶ ¬ timedOut ls t}
    {_ : auto∶ IncludesHonest tms}
    {_ : auto∶ r ≥ ls .r-cur}
    → p ⦂ t ⊢ ls —[ m ]—→ recordTimeout ls
  ≪EnoughTimeouts? _ {x}{y}{z}{w} =
    EnoughTimeouts (toWitness x) (toWitness y) (toWitness z) (toWitness w)

  ≪TimerExpired? : let m = Timeout _ in
    {h : auto∶ ls .phase ≡ Receiving}
    {_ : auto∶ timedOut ls t}
    → p ⦂ t ⊢ ls —[ m ]—→ recordTimeout ls
  ≪TimerExpired? {h = x}{y} = TimerExpired (toWitness x) (toWitness y)

  ≪AdvanceRoundQC? : ∀ qc →
    {_ : auto∶ ls .phase ≡ AdvancingRound}
    {_ : auto∶ qc ∙∈ ls .db}
    {_ : auto∶ qc ∙round ≥ ls .r-cur}
    → p ⦂ t ⊢ ls ——→ advanceRound (inj₁ qc) ls
  ≪AdvanceRoundQC? _ {x}{y}{z} =
    AdvanceRoundQC (toWitness x) (toWitness y) (toWitness z)

  ≪AdvanceRoundTC? : ∀ tc →
    {_ : auto∶ ls .phase ≡ AdvancingRound}
    {_ : auto∶ tc ∙∈ ls .db}
    {_ : auto∶ tc ∙round ≥ ls .r-cur}
    → p ⦂ t ⊢ ls ——→ advanceRound (inj₂ tc) ls
  ≪AdvanceRoundTC? _ {x}{y}{z} =
    AdvanceRoundTC (toWitness x) (toWitness y) (toWitness z)

  ≪AdvanceRoundNoOp? :
    {h : auto∶ ls .phase ≡ AdvancingRound}
    {_ : auto∶ AllQC (λ qc → qc ∙round < ls .r-cur) (ls .db)}
    {_ : auto∶ AllTC (λ tc → tc ∙round < ls .r-cur) (ls .db)}
    → p ⦂ t ⊢ ls ——→ record ls { phase = Locking }
  ≪AdvanceRoundNoOp? {h = x}{y}{z} =
    AdvanceRoundNoOp (toWitness x) (toWitness y) (toWitness z)

  ≪Lock? :
    {h : auto∶ ls .phase ≡ Locking}
    {_ : auto∶ qc -highest-qc-∈- ls .db}
    → p ⦂ t ⊢ ls ——→ lock qc ls
  ≪Lock? {h = x}{y} = Lock (toWitness x) (toWitness y)

  ≪Commit? : ∀ b ch →
    {_ : auto∶ ls .phase ≡ Committing}
    {_ : auto∶ b ∶ ch longer-final-∈ ls}
    → p ⦂ t ⊢ ls ——→ commit ch ls
  ≪Commit? _ _ {x}{y} = Commit (toWitness x) (toWitness y)

  ≪CommitNoOp? :
    {h : auto∶ ls .phase ≡ Committing}
    {_ : auto∶ NoBlock (_longer-final-∈ ls) (ls .db)}
    → p ⦂ t ⊢ ls ——→ record ls {phase = Voting}
  ≪CommitNoOp? {h = x}{y} = CommitNoOp (toWitness x) (toWitness y)

  ≪VoteBlock? : ∀ b →
    let
      m  = Vote $ signData p (b ∙blockId , b ∙round)
      L′ = roundLeader (1 + ls .r-cur)
    in
    {_ : auto∶ ls .phase ≡ Voting}
    {_ : auto∶ b ∙∈ ls .db}
    {_ : auto∶ ShouldVote ls b}
    → p ⦂ t ⊢ ls —[ L′ ∣ m ⟩—→ voteProposal ls
  ≪VoteBlock? _ {x}{y}{z} = VoteBlock (toWitness x) (toWitness y) (toWitness z)

  ≪VoteBlockNoOp? :
   {h : auto∶ ls .phase ≡ Voting}
   {_ : auto∶  NoBlock (ShouldVote ls) (ls .db)}
   → p ⦂ t ⊢ ls ——→ shouldEnterRound ls
  ≪VoteBlockNoOp? {h = x}{y} = VoteBlockNoOp (toWitness x) (toWitness y)

module _ {s : GlobalState} (let t = s .currentTime) where
  module _ p ⦃ _ : Honest p ⦄ (let ls = s ＠ p; L = currentLeader ls) where
    _:InitTC? :
      {h : auto∶ ls .phase ≡ EnteringRound}
      {_ : auto∶ ls .tc-last ≡ just tc}
      → s —→ _
    _:InitTC? {h = x}{y} = LocalStep $′ ≪InitTC? p {h = x}{y}

    _:InitNoTC? :
      {_ : auto∶ ls .phase ≡ EnteringRound}
      {_ : auto∶ ls .tc-last ≡ nothing}
      → s —→ _
    _:InitNoTC? {x}{y} = LocalStep $′ ≪InitNoTC? p {h = x}{y}

    _:ProposeBlock?_ : ∀ txn →
      {_ : auto∶ ls .phase ≡ Proposing}
      {_ : auto∶ p ≡ L}
      → s —→ _
    _:ProposeBlock?_ txn {x}{y} = LocalStep $′ ≪ProposeBlock? _ txn {x}{y}

    _:ProposeBlockNoOp? :
      {_ : auto∶ ls .phase ≡ Proposing}
      {_ : auto∶ p ≢ L}
      → s —→ _
    _:ProposeBlockNoOp? {x}{y} = LocalStep $′ ≪ProposeBlockNoOp? _ {h = x}{y}

    _:RegisterProposal? : let m = _; b = sb .datum in
      {m∈ : auto∶ m ∈ ls .inbox}
      {_  : auto∶ ls .phase ≡ Receiving}
      {_  : auto∶ ¬ timedOut ls t}
      {_  : auto∶ sb .node ≡ roundLeader (b ∙round)}
      {_  : auto∶ ValidProposal (ls .db) b}
      → s —→ _
    _:RegisterProposal? {m∈ = x}{y}{z}{w}{q} = LocalStep $′
      ≪RegisterProposal? _ {m∈ = x}{y}{z}{w}{q}

    _:RegisterVote?_ : ∀ b {p′} → let L′ = roundLeader (1 + r); m = _ in
      {_ : auto∶ m ∈ ls .inbox}
      {_ : auto∶ ls .phase ≡ Receiving}
      {_  : auto∶ ¬ timedOut ls t}
      {_ : auto∶ b ∙∈ ls .db}
      {_ : auto∶ m ∉ ls .db}
      {_ : auto∶ L′ ≡ p}
      → s —→ _
    _:RegisterVote?_ b {p′}{x}{y}{z}{w}{q}{k} =
      LocalStep $′ ≪RegisterVote? _ b p′ {x}{y}{z}{w}{q}{k}

    _:RegisterTimeout?_ : ∀ tm → let m = Timeout tm in
      {m∈ : auto∶ m ∈ ls .inbox}
      {_ : auto∶ ls .phase ≡ Receiving}
      {_ : auto∶ ¬ timedOut ls t}
      {_ : auto∶ m ∉ ls .db}
      → s —→ _
    _:RegisterTimeout?_ _ {x}{y}{z}{w} = LocalStep $′ ≪RegisterTimeout? _ _ {x}{y}{z}{w}

    _:RegisterTC? : let m = TCFormed tc in
      {m∈ : auto∶ m ∈ ls .inbox}
      {_  : auto∶ ls .phase ≡ Receiving}
      {_  : auto∶ ¬ timedOut ls t}
      {_  : auto∶ m  ∉ ls .db}
      → s —→ _
    _:RegisterTC? {m∈ = x}{y}{z}{w} = LocalStep $′ ≪RegisterTC? _ {m∈ = x}{y}{z}{w}

    _:EnoughTimeouts?_ : ∀ r → let tms = filter (IsTimeoutForRound? r) (ls .db) in
      {_ : auto∶ ls .phase ≡ Receiving}
      {_ : auto∶ ¬ timedOut ls t}
      {_ : auto∶ IncludesHonest tms}
      {_ : auto∶ r ≥ ls .r-cur}
      → s —→ _
    _:EnoughTimeouts?_ _ {x}{y}{z}{w} = LocalStep $′ ≪EnoughTimeouts? _ _ {x}{y}{z}{w}

    _:TimerExpired? :
      {_ : auto∶ ls .phase ≡ Receiving}
      {_ : auto∶ timedOut ls t}
      → s —→ _
    _:TimerExpired? {x}{y} = LocalStep $′ ≪TimerExpired? _ {h = x}{y}

    _:AdvanceRoundQC?_ : ∀ qc → let r = qc ∙round in
      {_ : auto∶ ls .phase ≡ AdvancingRound}
      {_ : auto∶ qc ∙∈ ls .db}
      {_ : auto∶ r ≥ ls .r-cur}
      → s —→ _
    _:AdvanceRoundQC?_ qc {x}{y}{z} = LocalStep $′ ≪AdvanceRoundQC? _ qc {x}{y}{z}

    _:AdvanceRoundTC?_ : ∀ tc → let r = tc ∙round in
      {_ : auto∶ ls .phase ≡ AdvancingRound}
      {_ : auto∶ tc ∙∈ ls .db}
      {_ : auto∶ r ≥ ls .r-cur}
      → s —→ _
    _:AdvanceRoundTC?_ tc {x}{y}{z} = LocalStep $′ ≪AdvanceRoundTC? _ tc {x}{y}{z}

    _:AdvanceRoundNoOp? :
      {_ : auto∶ ls .phase ≡ AdvancingRound}
      {_ : auto∶ AllQC (λ qc → qc ∙round < ls .r-cur) (ls .db)}
      {_ : auto∶ AllTC (λ tc → tc ∙round < ls .r-cur) (ls .db)}
      → s —→ _
    _:AdvanceRoundNoOp? {x}{y}{z} = LocalStep $′ ≪AdvanceRoundNoOp? _ {h = x}{y}{z}

    _:Lock? :
      {h : auto∶ ls .phase ≡ Locking}
      {_ : auto∶ qc -highest-qc-∈- ls .db}
      → s —→ _
    _:Lock? {h = x}{y} = LocalStep $′ ≪Lock? _ {h = x}{y}

    _:Commit?_ : ∀ (bch : Chain) {b ch} → ⦃ bch ≡ b ∷ ch ⦄ →
      {_ : auto∶ ls .phase ≡ Committing}
      {_ : auto∶ b ∶ ch longer-final-∈ ls}
      → s —→ broadcast (s .currentTime) nothing (s ＠ p ≔ commit ch ls)
    _:Commit?_ _ ⦃ refl ⦄ {x}{y} = LocalStep $′ ≪Commit? p _ _ {x}{y}

    _:CommitNoOp? :
      {_ : auto∶ ls .phase ≡ Committing}
      {_ : auto∶ NoBlock (_longer-final-∈ ls) (ls .db)}
      → s —→ _
    _:CommitNoOp? {x}{y} = LocalStep $′ ≪CommitNoOp? _ {h = x}{y}

    _:VoteBlock?_ : ∀ b →
      {_ : auto∶ ls .phase ≡ Voting}
      {_ : auto∶ b ∙∈ ls .db}
      {_ : auto∶ ShouldVote ls b}
      → s —→ _
    _:VoteBlock?_ b {x}{y}{z} = LocalStep $′ ≪VoteBlock? _ b {x}{y}{z}

    _:VoteBlockNoOp? :
      {_ : auto∶ ls .phase ≡ Voting}
      {_ : auto∶ NoBlock (ShouldVote ls) (ls .db)}
      → s —→ _
    _:VoteBlockNoOp? {x}{y} = LocalStep $′ ≪VoteBlockNoOp? _ {h = x}{y}

  module _ tpm {tpm∈ : auto∶ tpm ∈ s .networkBuffer} where

    Deliver? : s —→ _
    Deliver?  = Deliver (toWitness tpm∈)

  WaitUntil? : ∀ t →
    {_ : auto∶ All (λ (t′ , _ , _) → t ≤ t′ + Δ) (s .networkBuffer) }
    {_ : auto∶ currentTime s < t }
    → s —→ _
  WaitUntil? t {x}{y} = WaitUntil t (toWitness x) (toWitness y)
```
