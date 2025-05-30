<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Decidability.Core (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
private variable A B : Type
```
-->

## Decidability procedures

Decidability procedures to check that a given QC, TC or Chain is in a list of messages.

```agda
instance
  Dec-connects : _-connects-to-_ ⁇²
  Dec-connects .dec with dec | dec | dec
  ... | yes p | yes q | yes r = yes (connects∶ p q r)
  ... | no ¬p | _     | _     = no λ where (connects∶ p _ _) → ¬p p
  ... | _     | no ¬q | _     = no λ where (connects∶ _ q _) → ¬q q
  ... | _     | _     | no ¬r = no λ where (connects∶ _ _ r) → ¬r r

  Dec-qc∈-Message : _qc∈-Message_ ⁇²
  Dec-qc∈-Message {x = qc} {y = Propose sb} .dec
    with dec
  ... | yes eq = yes (qc∈-Propose eq)
  ... | no ¬eq
    with sb ∙tc? in eq
  ... | nothing = no λ where
    (qc∈-Propose eq) → ¬eq eq
    (qc∈-ProposeTC eq′ _) → contradict $ trans (sym eq) eq′
  ... | just tc
    with dec
  ... | yes qc∈ = yes (qc∈-ProposeTC eq qc∈)
  ... | no  qc∉ = no λ where
    (qc∈-Propose eq) → ¬eq eq
    (qc∈-ProposeTC eq′ qc∈) →
      qc∉ (subst (λ ◆ → qc ∈₁ qcs⁺ ◆)
          (M.just-injective (sym $ trans (sym eq) eq′))
          qc∈)
  Dec-qc∈-Message {y = Vote _} .dec = no λ ()
  Dec-qc∈-Message {y = TCFormed _} .dec with dec
  ... | yes qc∈ = yes (qc∈-TCFormed qc∈)
  ... | no ¬qc∈ = no λ where (qc∈-TCFormed qc∈) → ¬qc∈ qc∈
  Dec-qc∈-Message {y = Timeout (te , mtc)} .dec with dec
  ... | yes eq = yes (qc∈-Timeout eq)
  ... | no ¬eq
    with mtc in eq
  ... | nothing = no λ where
    (qc∈-Timeout eq) → ¬eq eq
    (qc∈-TimeoutTC eq′ _ ) → contradict eq′
  ... | just tc
    with dec
  ... | yes qc∈ = yes (qc∈-TimeoutTC refl qc∈)
  ... | no qc∉ = no λ where
    (qc∈-Timeout eq) → ¬eq eq
    (qc∈-TimeoutTC refl qc∈) → qc∉ qc∈
  Dec-tc∈-Message : _tc∈-Message_ ⁇²
  Dec-tc∈-Message {y = Propose _} .dec with dec
  ... | yes eq = yes (tc∈-Propose eq)
  ... | no ¬eq = no λ where (tc∈-Propose eq) → ¬eq eq
  Dec-tc∈-Message {y = Vote _} .dec = no λ ()
  Dec-tc∈-Message {tc}{TCFormed tc′} .dec with tc′ ≟ tc
  ... | yes refl = yes tc∈-TCFormed
  ... | no ¬eq   = no λ where tc∈-TCFormed → ¬eq refl
  Dec-tc∈-Message {y = Timeout x} .dec with dec
  ... | yes eq = yes (tc∈-Timeout eq)
  ... | no ¬eq = no λ where (tc∈-Timeout eq) → ¬eq eq

  Dec-qc-∈ : _-qc-∈-_ ⁇²
  Dec-qc-∈ .dec with dec
  ... | yes eq = yes (initialQC eq)
  ... | no ¬eq with dec
  ... | yes qc∈ = yes (receivedQC qc∈)
  ... | no  qc∉ with dec
  ... | yes all∈ = yes (formedQC all∈)
  ... | no ¬all∈ = no λ where
    (initialQC eq) → ¬eq eq
    (formedQC all∈) → ¬all∈ all∈
    (receivedQC x) → qc∉ x

  Dec-te∈ : _-te-∈-_ ⁇²
  Dec-te∈ {y = []} .dec = no λ where (_ , ())
  Dec-te∈ {y = Propose _ ∷ _} .dec with dec
  ... | no ¬mtc×m∈ = no (λ where (mtc , there m∈) → ¬mtc×m∈ (mtc , m∈))
  ... | yes m∈ = yes (proj₁ m∈ , there (proj₂ m∈))
  Dec-te∈ {y = Vote _ ∷ _} .dec with dec
  ... | no ¬mtc×m∈ = no (λ where (mtc , there m∈) → ¬mtc×m∈ (mtc , m∈))
  ... | yes m∈ = yes (proj₁ m∈ , there (proj₂ m∈))
  Dec-te∈ {y = TCFormed _ ∷ _} .dec with dec
  ... | no ¬mtc×m∈ = no (λ where (mtc , there m∈) → ¬mtc×m∈ (mtc , m∈))
  ... | yes m∈ = yes (proj₁ m∈ , there (proj₂ m∈))
  Dec-te∈ {te} {Timeout (te′ , _) ∷ _} .dec with te ≟ te′
  ... | yes refl = yes (-, here refl)
  ... | no ¬eq with dec
  ... | no ¬mtc×m∈ = no λ where
    (mtc , here refl) → ¬eq refl
    (mtc , there m∈)  → ¬mtc×m∈ (-, m∈)
  ... | yes m∈ = yes (m∈ .proj₁ , there (m∈ .proj₂))

  Dec-tc∈ : _-tc-∈-_ ⁇²
  Dec-tc∈ .dec with dec
  ... | yes ftc = yes (formedTC ftc)
  ... | no ¬ftc with dec
  ... | yes tc∈ = yes (receivedTC tc∈)
  ... | no  ¬tc = no λ where
    (formedTC x)   → ¬ftc x
    (receivedTC x) → ¬tc x

  Dec-chain-∈ : _-chain-∈-_ ⁇²
  Dec-chain-∈ {[]} {ms} .dec = yes []
  Dec-chain-∈ {b ∷ ch} {ms} .dec
    with b ∙∈? ms
  ... | no ¬p = no λ where (p ∷ _ ⊣ _) → ¬p p
  ... | yes p with ¿ ch -chain-∈- ms ¿
  ... | no ¬q = no (λ where (_ ∷ q ⊣ _) → ¬q q)
  ... | yes q with ¿ b -connects-to- ch ¿
  ... | no ¬w = no λ where (_ ∷ _ ⊣ w) →  ¬w w
  ... | yes w = yes (p ∷ q ⊣ w)

_ = Decidable²  _-qc-∈-_
  ∋ dec²

_ = Decidable²  _-tc-∈-_
  ∋ dec²

_ = Decidable²  _-chain-∈-_
  ∋ dec²

UniqueMajority⊆ˢ : List A → Type
UniqueMajority⊆ˢ xs = ∃ λ ys →
    ys ⊆ˢ xs
  × Unique ys
  × IsMajority ys

UniqueByMajority⊆ˢ : (f : B → A) → List B → Type
UniqueByMajority⊆ˢ f xs = ∃ λ ys →
    ys ⊆ˢ xs
  × UniqueBy f ys
  × IsMajority ys

module _ ⦃ _ : DecEq A ⦄ where instance
  Dec-UniqueMajority⊆ˢ : UniqueMajority⊆ˢ {A = A} ⁇¹
  Dec-UniqueMajority⊆ˢ {x = xs} .dec
    with ¿ IsMajority (nub xs) ¿
  ... | yes maj = yes (nub xs , nub-⊆⁻ , Unique-nub {xs = xs} , maj)
  ... | no ¬maj = no λ (ys , ys⊆ˢ , u , m) →
    ¬maj $ majority-mono u (L.SubS.⊆-trans ys⊆ˢ nub-⊆⁺) m

  Dec-UniqueByMajority⊆ˢ : {f : B → A} →  UniqueByMajority⊆ˢ {A = A} f ⁇¹
  Dec-UniqueByMajority⊆ˢ {f = f} {xs} .dec
    with ¿ IsMajority (nubBy f xs) ¿
  ... | yes maj = yes (nubBy f xs , nubBy-⊆⁻ f ,  UniqueBy-nubBy f xs  , maj)
  ... | no ¬maj = no λ (ys , ys⊆ˢ , u , m) →
    ¬maj ( majority-map⁻ (nubBy f xs) f
         $ majority-mono u
             (L.SubS.⊆-trans (L.SubS.map⁺ f ys⊆ˢ) $ nubBy-⊆⁺ f {xs = xs})
             (majority-map⁺ ys f m)
         )

instance
  Dec-AllBlock : ∀ {P : Block → Type} → ⦃ P ⁇¹ ⦄ → AllBlock P ⁇¹
  Dec-AllBlock {P}{ms} .dec with ¿ All P (allBlocks ms) ¿
  ... | yes allp = yes $ mk (L.All.lookup allp)
  ... | no ¬allp = no λ where (mk f) → ¬allp $ L.All.tabulate f
```
