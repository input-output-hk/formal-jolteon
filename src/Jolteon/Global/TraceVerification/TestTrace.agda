{-# OPTIONS --safe #-}

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.TraceVerification.TestTrace (⋯ : _) (open Assumptions ⋯) where

open import Prelude
open import Prelude.Result

open import Jolteon.Global.TraceVerification.ToSpec

open import Jolteon.Decidability ⋯

module Spec where
  open import Jolteon.Block ⋯ public
  open import Jolteon.Message ⋯ public

open import Jolteon.Local.State ⋯
open import Jolteon.Local.Step ⋯

open import Jolteon.Global.State ⋯
open import Jolteon.Global.Step ⋯
open import Jolteon.Global.Trace ⋯

open Spec hiding ( Block; TC; QC; Chain
                 ; TimeoutMessage; TimeoutEvidence
                 ; ThresholdSig; Signed)

private variable
  A B : Type

-- Looking up keys

instance
  ToSpecPublicKey : ToSpec PublicKey Pid TodoErr
  ToSpecPublicKey .fromSpec = _∙pk
  ToSpecPublicKey .toSpec pk = decResult (lookupKey pk) `mapErr` λ _ → _

-- Trivial instances

instance
  ToSpecℕ : ∀ {E} → ToSpec ℕ ℕ E
  ToSpecℕ = IdToSpec

-- Signatures

record Signed (A : Type) : Type where
  constructor _signed-by_
  field payload : A
        key     : PublicKey

instance
  -- Only safe if the ToSpec A B instance preserves digests!
  ToSpecSigned : ⦃ ToSpec A B TodoErr ⦄ → ToSpec (Signed A) (Spec.Signed B) TodoErr
  ToSpecSigned .fromSpec (x signed-by p) = fromSpec x signed-by fromSpec p
  ToSpecSigned .toSpec (x signed-by pk) = do
    (x , p) , refl ← toSpec (x , pk)
    return (x signed-by p , refl)

-- -- Threshold signatures

record ThresholdSig (A : Type) : Type where
  field
    payload : A
    shares  : List PublicKey

instance
  ToSpecThresholdSig : ToSpec (ThresholdSig A) (Spec.ThresholdSig A) TodoErr
  ToSpecThresholdSig .fromSpec sig = record{ payload = sig .payload
                                           ; shares  = map _∙pk (sig .shares) }
  ToSpecThresholdSig .toSpec record{payload = p; shares = keys} = do
    let work = toSpec keys -- Work around ToSpec instance being solved too late
    shares , refl ← work
    uniqueShares  ← ¿ Unique shares     ¿ᴿ: λ _ → _
    quorum        ← ¿ IsMajority shares ¿ᴿ: λ _ → _
    return ( record{ payload      = p
                   ; shares       = shares
                   ; uniqueShares = uniqueShares
                   ; quorum       = quorum }
           , refl
           )

-- QC

QC = ThresholdSig (BlockId × Round)

-- TC

TimeoutEvidence = Signed (Round × QC)

record TC : Type where
  field
    roundTC : Round
    tes     : List TimeoutEvidence

instance
  ToSpecTC : ToSpec TC Spec.TC TodoErr
  ToSpecTC .fromSpec tc = record{ roundTC = tc .roundTC
                                ; tes     = fromSpec (tc .tes) }
  ToSpecTC .toSpec record{ roundTC = r; tes = tes } = do
    let work = toSpec tes -- Work around instance argument being solved too late
    tes , refl ← work
    quorumTC ← ¿ IsMajority tes                       ¿ᴿ: λ _ → _
    uniqueTC ← ¿ UniqueBy node tes                    ¿ᴿ: λ _ → _
    allRound ← ¿ All (λ te → te ∙round       ≡ r) tes ¿ᴿ: λ _ → _
    qcBound  ← ¿ All (λ te → te ∙qcTE ∙round < r) tes ¿ᴿ: λ _ → _
    let tc = record{ roundTC  = r
                    ; tes      = tes
                    ; quorumTC = quorumTC
                    ; uniqueTC = uniqueTC
                    ; allRound = allRound
                    ; qcBound  = qcBound
                    }
    return (tc , refl)

TimeoutMessage = TimeoutEvidence × Maybe TC

-- Blocks

record Block : Type where
  field
    blockQC : QC
    blockTC : Maybe TC
    round   : Round
    txs     : List Transaction

instance
  ToSpecBlock : ToSpec Block Spec.Block TodoErr
  ToSpecBlock .fromSpec b = record{ blockQC = fromSpec (b .blockQC)
                                  ; blockTC = fromSpec (b .blockTC)
                                  ; round   = b .round
                                  ; txs     = b .txs }
  ToSpecBlock .toSpec record{ blockQC = qc
                            ; blockTC = tc
                            ; round   = r
                            ; txs     = txs } = do
    qc , refl ← toSpec qc
    let work = toSpec tc
    tc , refl ← work
    return (⟨ qc , tc , r , txs ⟩ , refl)
