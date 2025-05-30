{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Core (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯

-- Assume that a hash of a chain is never equal to a hash of a block.
Genesis ¬Genesis : ∀ {A} → ⦃ HasBlockId A ⦄ → A → Type
Genesis  x = x ∙blockId ≡ genesisId
¬Genesis x = ¬ Genesis x

_-certified-by-_ : Block → QC → Type
B -certified-by- QC
  = QC ∙blockId ≡ B ∙blockId
  × QC ∙round   ≡ B ∙round

¬certified-by-genesis :
  b -certified-by- qc
  ───────────────────
  ¬Genesis qc
¬certified-by-genesis (id≡ , _) refl = noHashCollision id≡

¬certified-by-qc₀ : ¬ b -certified-by- qc₀
¬certified-by-qc₀ {b} cb = ¬certified-by-genesis {qc = qc₀} cb refl

certified-by-trans : ∀ {b qc qc′} → qc ≡ qc′ → b -certified-by- qc → b -certified-by- qc′
certified-by-trans refl bc = bc

_←—_←—_ : Block → QC → Block → Type
Bᵢ ←— QCᵢ ←— Bᵢ₊₁
  = Bᵢ -certified-by- QCᵢ
  × QCᵢ ≡ Bᵢ₊₁ .blockQC

_←—_ : Block → Block → Type
Bᵢ ←— Bᵢ₊₁ = Bᵢ -certified-by- Bᵢ₊₁ .blockQC

←—⇒¬cert₀ :
  b ←— b′
  ───────────
  ¬Genesis b′
←—⇒¬cert₀ {b}{b′} (cb , refl) id≡ = noHashCollision (sym id≡)

←—-inj :
  ∙ (b  ←— b″)
  ∙ (b′ ←— b″)
    ──────────
    b ≡ b′
←—-inj (refl , refl) (p , q) = ♯-inj p

CertifiedBlock : Pred Block 0ℓ
CertifiedBlock B = ∃ (B -certified-by-_)

CertifiedBlockIn : Messages → Block → Type
CertifiedBlockIn ms B = ∃ λ qc
  → B -certified-by- qc
  × qc ∙∈ ms

¬certified-in₀ :
  CertifiedBlockIn ms b
  ─────────────────────
  ¬Genesis b
¬certified-in₀ {b = b} (qc , cb@(refl , _) , _) = ¬certified-by-genesis {b}{qc} cb

GloballyCertifiedBlockIn : GlobalState → Block → Type
GloballyCertifiedBlockIn s B = CertifiedBlockIn (s .history) B

data _←—∗_ : Rel Block 0ℓ where
  stop :
    {- empty / reflexive -}
    ───────
    b ←—∗ b

    -- {- non-empty / non-reflexive -}
    -- b ←— qc ←— b′
    -- ─────────────
    -- b ←—∗ b′

  continue :
    -- {- cons -}
    -- ∙ b  ←— qc  ←— b′
    -- ∙ b′ ←—∗ b″

    {- snoc -}
    ∙ b  ←—∗ b′
    ∙ b′ ←— qc ←— b″
      ───────────────
      b ←—∗ b″

pattern
  -- {- cons -} stop¹ b← = continue (b← , refl) stop
  {- snoc -} stop¹ b← = continue stop (b← , refl)

←∗-trans :
  ∙ b  ←—∗ b′
  ∙ b′ ←—∗ b″
    ─────────
    b  ←—∗ b″
←∗-trans stop q = q
←∗-trans p stop = p
←∗-trans p@(continue _ _) (continue q r) = continue (←∗-trans p q) r

←∗-factor :
  ∙ b  ←—∗ b″
  ∙ b′ ←—∗ b″
    ──────────
    b  ←—∗ b′
  ⊎ b′ ←—∗ b
←∗-factor stop q = inj₂ q
←∗-factor p stop = inj₁ p
←∗-factor (continue {b″ = b″} p (q , refl)) (continue p′ (q′ , refl))
  -- rewrite ←—-inj {b″ = b″} q q′
  = ←∗-factor p (subst (_ ←—∗_) (sym $ ←—-inj {b″ = b″} q q′) p′)
--   = ←∗-factor p p′

b∈⇒b← :
  ∙ ValidChain (b′ ∷ ch)
  ∙ b ∈ b′ ∷ ch
    ────────────────────
    b ←—∗ b′
b∈⇒b← (_ ∷ _ ⊣ _) (here refl) = stop
b∈⇒b← {b′}{ch}{b} (.b′ ∷ vch ⊣ ←b′) (there {xs = b″ ∷ _} b∈) = b←b′
  where
  b←b″ : b ←—∗ b″
  b←b″ = b∈⇒b← vch b∈

  st : b″ ←— b′ .blockQC ←— b′
  st = (←b′ .idMatch , ←b′ .roundMatch) , refl

  b←b′ : b ←—∗ b′
  b←b′ = continue b←b″ st
