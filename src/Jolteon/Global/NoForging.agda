{-# OPTIONS --safe #-}
open import Prelude

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.NoForging (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
open import Jolteon.Message ⋯
open import Jolteon.Global.State ⋯

data 𝕌 : Type where
  BR RQ B : 𝕌

⟦_⟧ : 𝕌 → Type
⟦_⟧ = λ where
  BR → BlockId × Round
  RQ → Round × QC
  B  → Block

data _-∈-QC-_ : Signed ⟦ BR ⟧ → QC → Type where
  ∈-QC :
    p ∈ qc .shares
    ───────────────────────────────────
    (qc .payload signed-by p) -∈-QC- qc

data _-∈-TE-_ : ∀ {u} → Signed ⟦ u ⟧ → TimeoutEvidence → Type

_∶_-∈-TE-_ : ∀ u → Signed ⟦ u ⟧ → TimeoutEvidence → Type
_∶_-∈-TE-_ u = _-∈-TE-_ {u = u}

data _-∈-TE-_ where
  ∈-TE :
    ────────────
    RQ ∶ te -∈-TE- te

  ∈-TE-QC : ∀ {sa} →
    sa -∈-QC- (te ∙qcTE)
    ────────────────────
    BR ∶ sa -∈-TE- te

private variable u : 𝕌

data _-∈-TC-_ : Signed ⟦ u ⟧ → TC → Type

_∶_-∈-TC-_ : ∀ u → Signed ⟦ u ⟧ → TC → Type
_∶_-∈-TC-_ u = _-∈-TC-_ {u = u}

data _-∈-TC-_ where
  ∈-TC : ∀ {sa : Signed ⟦ u ⟧} →
    Any (u ∶ sa -∈-TE-_) (tc .tes)
    ──────────────────────────
    sa -∈-TC- tc

data _-∈ᴹ-_ : Signed ⟦ u ⟧ → Message → Type

_∶_-∈ᴹ-_ : ∀ u → Signed ⟦ u ⟧ → Message → Type
_∶_-∈ᴹ-_ u su m = _-∈ᴹ-_ {u = u} su m

data _-∈ᴹ-_ where

  ∈-Propose :
    ─────────────
    sb -∈ᴹ- Propose sb

  ∈-Propose-QC : ∀ {sa} →
    sa -∈-QC- (sb ∙qc)
    ───────────────────────
    BR ∶ sa -∈ᴹ- Propose sb

  ∈-Propose-TC : ∀ {sa : Signed ⟦ u ⟧} →
    Any (sa -∈-TC-_) (sb ∙tc?)
    ──────────────────────────
    sa -∈ᴹ- Propose sb

  ∈-Vote : ∀ {vs : VoteShare} →
    ────────────────────
    BR ∶ vs -∈ᴹ- Vote vs

  ∈-TCFormed : ∀ {sa : Signed ⟦ u ⟧} →
    sa -∈-TC- tc
    ───────────────────
    sa -∈ᴹ- TCFormed tc

  ∈-Timeout-TE : ∀ {sa : Signed ⟦ u ⟧} →
    sa -∈-TE- te
    ──────────────────────────
    sa -∈ᴹ- Timeout (te , mtc)

  ∈-Timeout-TC : ∀ {sa : Signed ⟦ u ⟧} →
    Any (sa -∈-TC-_) mtc
    ──────────────────────────
    sa -∈ᴹ- Timeout (te , mtc)

NoSignatureForging : Message → GlobalState → Type
NoSignatureForging m s =

  ∀ {u} (sa : Signed ⟦ u ⟧) → sa -∈ᴹ- m →

    Honest (sa ∙pid)
    ───────────────────────────
    Any (sa -∈ᴹ-_) (s .history)
