{-# OPTIONS --safe #-}

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.TraceVerification.LocalStep (⋯ : _) (open Assumptions ⋯) where

open import Prelude
open import Prelude.Result

open import Jolteon.Global.TraceVerification.ToSpec
open import Jolteon.Global.TraceVerification.TestTrace ⋯

open import Jolteon.Decidability ⋯

open import Jolteon.Local.State ⋯
open import Jolteon.Local.Step ⋯

open import Jolteon.Global.State ⋯
open import Jolteon.Global.Step ⋯
open import Jolteon.Global.Trace ⋯

open Spec hiding ( TC; QC
                 ; TimeoutMessage; TimeoutEvidence
                 ; ThresholdSig; Signed)

data StepLabel : Type where
  InitTC InitNoTC  : StepLabel
  ProposeBlock     : List Transaction → StepLabel
  ProposeBlockNoOp : StepLabel
  RegisterProposal : BlockId → StepLabel
  RegisterVote     : Round → PublicKey → BlockId → StepLabel
  RegisterTimeout  : TimeoutMessage → StepLabel
  RegisterTC       : TC → StepLabel
  EnoughTimeouts   : Round → StepLabel
  TimerExpired     : StepLabel
  AdvanceRoundQC   : QC → StepLabel
  AdvanceRoundTC   : TC → StepLabel
  AdvanceRoundNoOp : StepLabel
  Lock             : QC → StepLabel
  Commit           : BlockId → StepLabel
  CommitNoOp       : StepLabel
  VoteBlock        : BlockId → StepLabel
  VoteBlockNoOp    : StepLabel

private variable
  ls₁ : LocalState
  s₁  : GlobalState
  lbl : StepLabel

stepLabel : p ⦂ t ⊢ ls — menv —→ ls′ → StepLabel
stepLabel (InitTC _ _)                                          = InitTC
stepLabel (InitNoTC _ _)                                        = InitNoTC
stepLabel (ProposeBlock {txn = txn} _ _)                        = ProposeBlock txn
stepLabel (ProposeBlockNoOp _ _)                                = ProposeBlockNoOp
stepLabel (RegisterProposal {sb = sb} _ _ _ _ _)                = RegisterProposal (sb .datum ∙blockId)
stepLabel (RegisterVote {r = r} {p′ = p′} {b = b} _ _ _ _ _ _)  = RegisterVote r (fromSpec p′) (b ∙blockId)
stepLabel (RegisterTimeout {tm = tm} _ _ _ _)                   = RegisterTimeout (fromSpec tm)
stepLabel (RegisterTC {tc = tc} _ _ _ _)                        = RegisterTC (fromSpec tc)
stepLabel (EnoughTimeouts {r = r} _ _ _ _)                      = EnoughTimeouts r
stepLabel (TimerExpired _ _)                                    = TimerExpired
stepLabel (AdvanceRoundQC {qc = qc} _ _ _)                      = AdvanceRoundQC (fromSpec qc)
stepLabel (AdvanceRoundTC {tc = tc} _ _ _)                      = AdvanceRoundTC (fromSpec tc)
stepLabel (AdvanceRoundNoOp _ _ _)                              = AdvanceRoundNoOp
stepLabel (Lock {qc = qc} _ _)                                  = Lock (fromSpec qc)
stepLabel (Commit {b = b} _ _)                                  = Commit (b ∙blockId)
stepLabel (CommitNoOp _ _)                                      = CommitNoOp
stepLabel (VoteBlock {b = b} _ _ _)                             = VoteBlock (b ∙blockId)
stepLabel (VoteBlockNoOp _ _)                                   = VoteBlockNoOp

findBlock : (bId : BlockId) (bs : List Spec.Block)
          → Result ⊤ (∃[ b ] b ∈ bs × bId ≡ b ∙blockId)
findBlock bId bs = findInList bs λ b → bId ≡ b ∙blockId

findBlockL : (bId : BlockId) (ls : LocalState)
          → Result ⊤ (∃[ b ] b ∙∈ ls .db × bId ≡ b ∙blockId)
findBlockL bId ls = findBlock bId (allBlocks (ls .db))

data IfPropose (P : Proposal → Type) : Message → Type where
  Propose : ∀ {sb} → P sb → IfPropose P (Propose sb)

data IfVote (P : VoteShare → Type) : Message → Type where
  Vote : ∀ {sb} → P sb → IfVote P (Vote sb)

instance
  Dec-IfPropose : ∀ {P} → ⦃ P ⁇¹ ⦄ → IfPropose P ⁇¹
  Dec-IfPropose {P = P} {Propose sb} .dec with ¿ P sb ¿
  ... | yes p = yes (Propose p)
  ... | no np = no λ where (Propose p) → np p
  Dec-IfPropose {x = Vote     _} .dec = no λ()
  Dec-IfPropose {x = TCFormed _} .dec = no λ()
  Dec-IfPropose {x = Timeout  _} .dec = no λ()

  Dec-IfVote : ∀ {P} → ⦃ P ⁇¹ ⦄ → IfVote P ⁇¹
  Dec-IfVote {P = P} {Vote sb} .dec with ¿ P sb ¿
  ... | yes p = yes (Vote p)
  ... | no np = no λ where (Vote p) → np p
  Dec-IfVote {x = Propose  _} .dec = no λ()
  Dec-IfVote {x = TCFormed _} .dec = no λ()
  Dec-IfVote {x = Timeout  _} .dec = no λ()

data Err-FindChain : Type where
  E-Step     : BlockId → Err-FindChain → Err-FindChain
  E-NoParent : BlockId → Err-FindChain
  E-BadRound : Round → Round → Err-FindChain
  E-Invalid  : BlockId → Spec.Block → Err-FindChain
  E-Cycle    : Err-FindChain

findChain' : ℕ → (b : Spec.Block) (ms : Messages) → b ∙∈ ms → ValidBlock b
           → Result Err-FindChain (Σ Spec.Chain λ ch → (b ∷ ch) ∙∈ ms)
findChain' 0 _ _ _ _ = Err E-Cycle
findChain' (suc fuel) b ms b∈ms vb = do
  let parentId    = b .blockQC ∙blockId
      parentRound = b .blockQC ∙round
  case parentId ≟ genesisId of λ where
    (yes isGenesis) → do
      rOk ← ¿ parentRound ≡ 0 ¿ᴿ: λ _ → E-BadRound parentRound 0
      return ([] , b∈ms ∷ [] ⊣ connects∶ isGenesis rOk vb)
    (no _) → do
      b′ , b′∈ms , idOk ← findBlock parentId (allBlocks ms) `mapErr` λ _ → E-NoParent parentId
      rOk               ← ¿ parentRound ≡ b′ ∙round ¿ᴿ: λ _ → E-BadRound parentRound (b′ ∙round)
      vb′               ← ¿ ValidBlock b′ ¿ᴿ: λ _ → E-Invalid (b′ ∙blockId) b′
      ch , ch∈ms        ← findChain' fuel b′ ms b′∈ms vb′ `mapErr` E-Step (b ∙blockId)
      return (b′ ∷ ch , (b∈ms ∷ ch∈ms ⊣ connects∶ idOk rOk vb))

findChain : (b : Spec.Block) (ms : Messages) → b ∙∈ ms
          → ValidBlock b → Result Err-FindChain (∃[ ch ] (b ∷ ch) ∙∈ ms)
findChain b ms = findChain' (length ms) b ms

data Err-FinalChain (bId : BlockId) (ls : LocalState) : Type where
  E-NoBlock       : Err-FinalChain bId ls
  E-InvalidBlock  : Err-FinalChain bId ls
  E-NoChain       : List (BlockId × BlockId) → Err-FindChain → Err-FinalChain bId ls
  E-NoLongerFinal : Err-FinalChain bId ls

idAndParent : Spec.Block → BlockId × BlockId
idAndParent b = b ∙blockId , b .blockQC ∙blockId

findLongerFinalChain : (bId : BlockId) (ls : LocalState)
                     → Result (Err-FinalChain bId ls)
                              (∃[ b ] ∃[ ch ] bId ≡ b ∙blockId × b ∶ ch longer-final-∈ ls)
findLongerFinalChain bId ls = do
  b , b∈ , idOk ← findBlockL bId ls `mapErr`          λ _ → E-NoBlock
  vb            ← ¿ ValidBlock b ¿ᴿ:                  λ _ → E-InvalidBlock
  ch , _        ← findChain b (ls .db) b∈ vb `mapErr` E-NoChain (L.map idAndParent (allBlocks (ls .db)))
  H             ← ¿ b ∶ ch longer-final-∈ ls ¿ᴿ:      λ _ → E-NoLongerFinal
  return (b , ch , idOk , H)

data Err-verifyLocal (t : Time) (p : Pid) ⦃ _ : Honest p ⦄
                   : (ls : LocalState)
                   → StepLabel → Type where
  E-Err : Err-verifyLocal t p ls lbl
  E-Commit : ∀ {bId}
           → Err-FinalChain bId ls
           → Err-verifyLocal t p ls (Commit bId)

verifyLocal : (t : Time) (p : Pid) ⦃ _ : Honest p ⦄ (lbl : StepLabel) (ls : LocalState)
            → Result (Err-verifyLocal t p ls lbl)
                     (∃[ menv ] ∃[ ls₁ ] Σ[ step ∈ p ⦂ t ⊢ ls — menv —→ ls₁ ] stepLabel step ≡ lbl)
verifyLocal t p  InitTC ls = do
  H₁      ← ¿ ls .phase ≡ EnteringRound ¿ᴿ: λ _ → E-Err
  tc , H₂ ← isJustᴿ (ls .tc-last) `mapErr` λ _ → E-Err
  return (just [ currentLeader ls ∣ TCFormed tc ⟩ , _ , InitTC H₁ H₂ , refl)
verifyLocal t p InitNoTC ls = do
  H₁ ← ¿ ls .phase ≡ EnteringRound ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ ls .tc-last ≡ nothing     ¿ᴿ: λ _ → E-Err
  return (nothing , _ , InitNoTC H₁ H₂ , refl)
verifyLocal t p (ProposeBlock txn) ls = do
  let b  = mkBlockForState ls txn
      L  = currentLeader ls
  H₁   ← ¿ ls .phase ≡ Proposing      ¿ᴿ: λ _ → E-Err
  H₂   ← ¿ p ≡ L                      ¿ᴿ: λ _ → E-Err
  return (just [ Propose (signData L b) ⟩ , _ , ProposeBlock H₁ H₂ , refl)
verifyLocal t p ProposeBlockNoOp ls = do
  let L  = currentLeader ls
  H₁   ← ¿ ls .phase ≡ Proposing ¿ᴿ: λ _ → E-Err
  H₂   ← ¿ p ≢ L                 ¿ᴿ: λ _ → E-Err
  return (nothing , _ , ProposeBlockNoOp H₁ H₂ , refl)
verifyLocal t p (RegisterProposal bId) ls = do
  Propose sb , m∈ , Propose (refl , H₃) ←
    findInList (ls .inbox) (IfPropose λ sb →
                              bId ≡ sb .datum ∙blockId
                            × sb .node ≡ roundLeader (sb .datum ∙round))
    `mapErr` λ _ → E-Err
  let L  = currentLeader ls
      b  = sb .datum
  H₁ ← ¿ ls .phase ≡ Receiving             ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ ¬ timedOut ls t                   ¿ᴿ: λ _ → E-Err
  H₄ ← ¿ ValidProposal (ls .db) b          ¿ᴿ: λ _ → E-Err
  return (nothing , _ , RegisterProposal m∈ H₁ H₂ H₃ H₄ , refl)
verifyLocal t p (RegisterVote r key bId) ls = do
  p′ , refl     ← toSpec key        `mapErr` λ _ → E-Err
  _ , b∈ , refl ← findBlockL bId ls `mapErr` λ _ → E-Err
  Vote sd@(_ signed-by _) , m∈ , Vote (refl , refl , refl) ←
    findInList (ls .inbox)
      (IfVote λ sd →
        bId ≡ sd .datum .proj₁
      × r   ≡ sd .datum .proj₂
      × p′  ≡ sd .node
      )
    `mapErr` λ _ → E-Err
  let L′ = roundLeader (1 + r)
      m  = Vote sd
  H₁ ← ¿ ls .phase ≡ Receiving ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ ¬ timedOut ls t       ¿ᴿ: λ _ → E-Err
  H₄ ← ¿ m ∉ ls .db            ¿ᴿ: λ _ → E-Err
  H₅ ← ¿ L′ ≡ p                ¿ᴿ: λ _ → E-Err
  return (nothing , _ , RegisterVote m∈ H₁ H₂ b∈ H₄ H₅ , refl)
verifyLocal t p (RegisterTimeout tm) ls = do
  tm , refl ← toSpec tm `mapErr` λ _ → E-Err
  let m  = Timeout tm
  m∈ ← ¿ m ∈ ls .inbox         ¿ᴿ: λ _ → E-Err
  H₁ ← ¿ ls .phase ≡ Receiving ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ ¬ timedOut ls t       ¿ᴿ: λ _ → E-Err
  H₃ ← ¿ m ∉ ls .db            ¿ᴿ: λ _ → E-Err
  return (nothing , _ , RegisterTimeout m∈ H₁ H₂ H₃ , refl)
verifyLocal t p (RegisterTC tc) ls = do
  tc , refl ← toSpec tc `mapErr` λ _ → E-Err
  let m  = TCFormed tc
  m∈ ← ¿ m ∈ ls .inbox         ¿ᴿ: λ _ → E-Err
  H₁ ← ¿ ls .phase ≡ Receiving ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ ¬ timedOut ls t       ¿ᴿ: λ _ → E-Err
  H₃ ← ¿ m ∉ ls .db            ¿ᴿ: λ _ → E-Err
  return (nothing , _ , RegisterTC m∈ H₁ H₂ H₃ , refl)
verifyLocal t p (EnoughTimeouts r) ls = do
  let sd  = signData p (ls .r-cur , ls .qc-high) , ls .tc-last
      tms = filter (IsTimeoutForRound? r) (ls .db)
  H₁   ← ¿ ls .phase ≡ Receiving ¿ᴿ: λ _ → E-Err
  H₂   ← ¿ ¬ timedOut ls t       ¿ᴿ: λ _ → E-Err
  H₃   ← ¿ IncludesHonest tms    ¿ᴿ: λ _ → E-Err
  H₄   ← ¿ r ≥ ls .r-cur         ¿ᴿ: λ _ → E-Err
  return (just [ Timeout sd ⟩ , _ , EnoughTimeouts H₁ H₂ H₃ H₄ , refl)
verifyLocal t p TimerExpired ls = do
  let sd  = signData p (ls .r-cur , ls .qc-high) , ls .tc-last
  H₁   ← ¿ ls .phase ≡ Receiving ¿ᴿ: λ _ → E-Err
  H₂   ← ¿ timedOut ls t         ¿ᴿ: λ _ → E-Err
  return (just [ Timeout sd ⟩ , _ , TimerExpired H₁ H₂ , refl)
verifyLocal t p (AdvanceRoundQC qc) ls = do
  qc , refl ← toSpec qc `mapErr`     λ _ → E-Err
  H₁ ← ¿ ls .phase ≡ AdvancingRound ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ qc ∙∈ ls .db               ¿ᴿ: λ _ → E-Err
  H₃ ← ¿ qc ∙round ≥ ls .r-cur      ¿ᴿ: λ _ → E-Err
  return (nothing , _ , AdvanceRoundQC H₁ H₂ H₃ , refl)
verifyLocal t p (AdvanceRoundTC tc) ls = do
  tc , refl ← toSpec tc `mapErr` λ _ → E-Err
  H₁ ← ¿ ls .phase ≡ AdvancingRound ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ tc ∙∈ ls .db               ¿ᴿ: λ _ → E-Err
  H₃ ← ¿ tc ∙round ≥ ls .r-cur      ¿ᴿ: λ _ → E-Err
  return (nothing , _ , AdvanceRoundTC H₁ H₂ H₃ , refl)
verifyLocal t p AdvanceRoundNoOp ls = do
  H₁ ← ¿ ls .phase ≡ AdvancingRound                    ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ AllQC (λ qc → qc ∙round < ls .r-cur) (ls .db) ¿ᴿ: λ _ → E-Err
  H₃ ← ¿ AllTC (λ tc → tc ∙round < ls .r-cur) (ls .db) ¿ᴿ: λ _ → E-Err
  return (nothing , _ , AdvanceRoundNoOp H₁ H₂ H₃ , refl)
verifyLocal t p (Lock qc) ls = do
  qc , refl ← toSpec qc `mapErr`     λ _ → E-Err
  H₁ ← ¿ ls .phase ≡ Locking      ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ qc -highest-qc-∈- ls .db ¿ᴿ: λ _ → E-Err
  return (nothing , _ , Lock H₁ H₂ , refl)
verifyLocal t p (Commit bId) ls = do
  H₁                ← ¿ ls .phase ≡ Committing ¿ᴿ: λ _ → E-Err
  _ , _ , refl , H₂ ← findLongerFinalChain bId ls `mapErr` E-Commit
  return (nothing , _ , Commit H₁ H₂ , refl)
verifyLocal t p CommitNoOp ls = do
  H₁ ← ¿ ls .phase ≡ Committing                ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ NoBlock (_longer-final-∈ ls) (ls .db) ¿ᴿ: λ _ → E-Err
  return (nothing , _ , CommitNoOp H₁ H₂ , refl)
verifyLocal t p (VoteBlock bId) ls = do
  b , b∈ , refl ← findBlockL bId ls `mapErr` λ _ → E-Err
  let sd  = signData p (b ∙blockId , b ∙round)
  H₁ ← ¿ ls .phase ≡ Voting ¿ᴿ: λ _ → E-Err
  H₃ ← ¿ ShouldVote ls b    ¿ᴿ: λ _ → E-Err
  return (just [ nextLeader ls ∣ Vote sd ⟩ , _ , VoteBlock H₁ b∈ H₃ , refl)
verifyLocal t p VoteBlockNoOp ls = do
  H₁ ← ¿ ls .phase ≡ Voting               ¿ᴿ: λ _ → E-Err
  H₂ ← ¿ NoBlock (ShouldVote ls) (ls .db) ¿ᴿ: λ _ → E-Err
  return (nothing , _ , VoteBlockNoOp H₁ H₂ , refl)
