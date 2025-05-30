<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Decidability.VoteSharesOf (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
```
-->
### The `voteShares` function and its properties

```agda

-- Obtain from ms a list of unique voteShares with the same blockId and round as d.
record VoteSharesOf (d : BlockId × Round) (ms : Messages) (vs : VoteShares) : Type where
  field
    complete : ∀ {v} → ⦃ v .datum ≡ d ⦄ → Vote v ∈ ms → v ∈ vs
    sound    : All (_∙∈ ms) vs
    datum≡   : All ((d ≡_) ∘ datum) vs
    unique   : Unique vs
    lemma    : vs ≡ map (d signed-by_) (map node vs)

  unique' : Unique (L.Mem.mapWith∈ vs λ {x} _ → x .node)
  unique' =
    Unique-mapWith∈⁺
    (λ where
      x∈ y∈ refl →
       cong (_signed-by _) $
         trans (sym $ L.All.lookup datum≡ x∈) (L.All.lookup datum≡ y∈)
    )
    unique

  unique′ : UniqueBy node vs
  unique′ = subst Unique (L.Mem.mapWith∈≗map node vs) unique'

open VoteSharesOf

voteShares⁺ : (d : BlockId × Round) (ms : Messages) → ∃ (VoteSharesOf d ms)
voteShares⁺ _ [] = [] , record
  { complete = λ ()
  ; sound    = []
  ; datum≡   = []
  ; unique   = []
  ; lemma    = refl
  }
voteShares⁺ d ms₀@(m ∷ ms)
  with vs , r ← voteShares⁺ d ms
  with vs⁺ ← (¬Vote m → ∃ (VoteSharesOf d ms₀)) ∋ (λ m≢ →
    vs , record
    { complete = λ where (here refl) → ⊥-elim m≢; (there v∈) → r .complete v∈
    ; sound    = L.All.map there (r .sound)
    ; datum≡   = r .datum≡
    ; unique   = r .unique
    ; lemma    = r .lemma
    })
  with m
... | Propose  _ = vs⁺ tt
... | TCFormed _ = vs⁺ tt
... | Timeout  _ = vs⁺ tt
... | Vote v
  with v .datum ≟ d
... | no d≢
  = vs , record
  { complete = λ where (here refl) → ⊥-elim (d≢ it); (there v∈) → r .complete v∈
  ; sound    = L.All.map there (r .sound)
  ; datum≡   = r .datum≡
  ; unique   = r .unique
  ; lemma    = r .lemma
  }
... | yes refl
  with v ∈? vs
... | no  v∉
  = v ∷ vs , record
  { complete = λ where (here refl) → here it; (there v∈) → there (r .complete v∈)
  ; sound    = here refl ∷ L.All.map there (r .sound)
  ; datum≡   = refl ∷ r .datum≡
  ; unique   = L.All.¬Any⇒All¬ _ v∉ ∷ r .unique
  ; lemma    = cong (_ ∷_) (r .lemma)
  }
  where
  v∈ : node v ∈ map node vs → v ∈ vs
  v∈ n∈
    with v , v′∈ , refl ← L.Mem.∈-map⁻ node n∈
    with refl ← L.All.lookup (r .datum≡) v′∈
    = v′∈
... | yes v∈
  = vs , record
  { complete = λ where (here refl) → v∈; (there v∈) → r .complete v∈
  ; sound    = L.All.map there (r .sound)
  ; datum≡   = r .datum≡
  ; unique   = r .unique
  ; lemma    = r .lemma
  }

module _ d ms (let vs , r = voteShares⁺ d ms) where
  voteShares : VoteShares
  voteShares = vs

  open VoteSharesOf r public renaming
    ( complete to voteShares-complete≡
    ; sound    to voteShares-sound
    ; datum≡   to voteShares-≡
    ; unique   to voteShares-Unique
    ; lemma    to voteShares-lemma
    )

voteShares-complete : ∀ {v ms} →
  Vote v ∈ ms
  ────────────────────────────
  v ∈ voteShares (v .datum) ms
voteShares-complete v∈ = voteShares-complete≡ _ _ v∈

-- Any formed-QC voteshares should be included in the voteShares for the QC payload.
-- (that is, voteShares is the maximal set of voteShares for the payload)
voteShares-maximal : ∀ qc ms →
  FormedQC qc ms
  ────────────────────────────────────────────────────
  qc .shares ⊆ˢ map node (voteShares (qc .payload) ms)
voteShares-maximal qc ms all∈ms {p} p∈qcshares =
  let
    vs = qc .payload signed-by p

    v∈ : Vote vs ∈ ms
    v∈ = L.All.lookup all∈ms (L.Mem.∈-map⁺ (_ signed-by_) p∈qcshares)

    vs∈ : vs ∈ voteShares (qc .payload) ms
    vs∈ = voteShares-complete v∈
  in
    L.Any.map⁺ $ L.Any.map (λ where refl → refl) vs∈
```
