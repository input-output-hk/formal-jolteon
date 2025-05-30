
{-# OPTIONS --safe #-}

open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Properties.Slice (⋯ : _) (open Assumptions ⋯) (p : Pid)⦃ hp : Honest p ⦄ where

open import Jolteon ⋯ hiding (p)
open import Jolteon.Local.Slice ⋯ p ⦃ hp ⦄
open import Jolteon.Properties.State.Messages ⋯

-- For every GlobalState, we can obtain a sliced stated
sliceState : GlobalState → SliceState
sliceState s = mkSliceState (s .currentTime) (s ＠ p) (s .history)

-- Every sliced state can be obtained by slicing a GlobalState
sliceState-surjective : Surjective _≡_ _≡_ sliceState
sliceState-surjective (mkSliceState t pls history) =
    mkGlobalState t (initStateMap [ p ]≔ pls) [] history
  , λ where refl → cong (λ ◆ → mkSliceState _ ◆ _)
                        (pLookup∘updateAt p ⦃ hp ⦄ {const pls} initStateMap)

_⊑_ : SliceState → SliceState → Type
ss ⊑ ss′ = ss .currentTime ≡ ss′ .currentTime
         × ss .pls ≡ ss′ .pls
         × ss .history ⊆ ss′ .history

⊑-refl : ss ⊑ ss
⊑-refl = refl , refl , L.SubL.⊆-refl

⊑-trans : ∀{ss ss′ ss″} → ss ⊑ ss′ → ss′ ⊑ ss″ → ss ⊑ ss″
⊑-trans (refl , refl ,  sh⊆) (refl , refl , sh⊆′) = refl , refl , L.SubL.⊆-trans sh⊆ sh⊆′

deliverMsg-slice : ∀ s m (tpm∈ : (t , p , m) ∈ s .networkBuffer) →
  sliceReceiveMessage m (sliceState s) .pls ≡ sliceState (deliverMsg s tpm∈) .pls
deliverMsg-slice s m tpm∈
  rewrite dec-yes (honest? p) hp .proj₂
  = sym $ pLookup∘updateAt p ⦃ hp ⦄ (s .stateMap)


sliceStep :
  (s′ ¹←— s)
  ──────────────────────────────────────────────────────
    sliceState s ⊑ sliceState s′
  ⊎ (sliceState s′ ←—ᴸ sliceState s)
sliceStep {s′}{s} (LocalStep {p = p′} {menv = menv} {ls′ = ls′} ⦃ hp′ ⦄ st)
  with p ≟ p′
... | no p≢
  rewrite pLookup∘updateAt′ p p′ ⦃ hp′ ⦄ {const ls′}
            (p≢ ∘ ↑-injective {∃p =  p ,· hp} {∃p′ = p′ ,· hp′})
            (s .stateMap)
  = inj₁ (refl , refl , h′⊆)
  where
  h′⊆ : _ ⊆ _
  h′⊆ with ⟫ menv
  ... | ⟫ nothing = L.SubL.⊆-refl
  ... | ⟫ just m  = _ ∷ʳ L.SubL.⊆-refl
... | yes refl
  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  = inj₂ $ LocalStep st
sliceStep {s = s} (DishonestLocalStep _ _) = inj₁ $ (refl , refl , _ ∷ʳ L.SubL.⊆-refl)
sliceStep {s′}{s} (Deliver {(t , p′ , m)} tpm∈) = QED
  where
  QED : sliceState s ⊑ sliceState s′
      ⊎ (sliceState s′ ←—ᴸ sliceState s)
  QED
     with p ≟ p′
  ... | yes refl
    rewrite (sym $ deliverMsg-slice s m tpm∈)
    = inj₂ $ Deliver m
  ... | no p≢
    with honest? p′
  ... | no ¬hp′ = inj₁ ⊑-refl
  ... | yes hp′ = inj₁ (refl
                       , (sym $ pLookup∘updateAt′ p p′ ⦃ hp′ ⦄ (p≢ ∘ ↑-injective) (s .stateMap))
                       , L.SubL.⊆-refl)
sliceStep {s = s}(WaitUntil t allt <t) = inj₂ $ WaitUntil t <t


slice-history-commute :  ∀{ss₀ ss₁ ss₂} →
  ss₀ ⊑ ss₁ →
  ss₂ ←—ᴸ ss₁
  ─────────────────────────────────
  ∃ (λ ss → (ss ←—ᴸ ss₀) × ss ⊑ ss₂)
slice-history-commute {ss₀} (refl , refl , s⊆) lst
  with lst
... | LocalStep {menv = menv}{ls′ = ls′} st =
  _ , LocalStep st , (refl , refl , s⊆′)
  where
  s⊆′ : _ ⊆ _
  s⊆′ with ⟫ menv
  ... | ⟫ nothing = s⊆
  ... | ⟫ just m = refl L.SubL.∷ s⊆
... | WaitUntil t x =
    _ , WaitUntil t x , (refl , refl , s⊆)
... | Deliver m =
    _ , Deliver m , (refl , refl ,  s⊆)

{-
 sliceTrace says that the local trace is as expressive as the global one
 (for the relevant data (i.e. the sliced state).
-}

sliceTrace :
  (s′ ↞— s)
  ──────────────────────────────────────────────────────
  ∃ λ ss′ → (ss′ ↞—ᴸ sliceState s) × ss′ ⊑ sliceState s′
sliceTrace (s ∎) = sliceState s , (_ ∎ᴸ) , ⊑-refl
sliceTrace {s = s₀} (s′ ⟨ st ∣ s ⟩←— tr)
  with ss , ss← , s⊑ ← sliceTrace tr
  with sliceStep st
... | inj₁ s⊑′ = ss , ss← , ⊑-trans s⊑ s⊑′
... | inj₂ ss←′ = let (ss , ss′← , ss⊑) = slice-history-commute s⊑ ss←′
      in ss , (_ ⟨ ss′← ⟩←—ᴸ ss←) , ss⊑

{-
The slice transition system is more general than the global transition system.
For example in the slite TS any message can be delivered, and there are no restrictions on how much time can advance. We say a slice step is valid, when these restrictions are met with respect to a global state.
-}

data SliceValidStep (s : GlobalState) : ∀ {ss′} → ss′ ←—ᴸ sliceState s → Type where
  LocalStepSound : ∀ menv ls′ →
    (let ss = sliceState s) →
    (st :  p ⦂ ss .currentTime ⊢ ss .pls — menv —→ ls′) →
    ──────────────────────────────────────────────────────
    SliceValidStep s (LocalStep st)

  DeliverSound : ∀ m →
    (tpm∈ : (t , p , m) ∈ s .networkBuffer) →
    ──────────────────────────────────────
    SliceValidStep s (Deliver m)

  WaitUntilSound : ∀ t →
    (<t : s .currentTime < t) →
    All (λ (t′ , _ , _) → t ≤ t′ + Δ) (s .networkBuffer)
    ────────────────────────────────────────────────────
    SliceValidStep s (WaitUntil t <t)

-- all the slice steps returned by sliceStep are valid.
sliceComplete : ∀ {lst} → (gst : s′ ¹←— s) →
  inj₂ lst ≡ sliceStep gst
  ────────────────────────
  SliceValidStep s lst
sliceComplete {s = s} (LocalStep {p = p′}{menv = menv} {ls′ = ls′} ⦃ hp′ ⦄ st) ≡inj₂
  with p ≟ p′
... | no p≢
  rewrite pLookup∘updateAt′ p p′ ⦃ hp′ ⦄ {const ls′}
           (p≢ ∘ ↑-injective {∃p =  p ,· hp} {∃p′ = p′ ,· hp′})
           (s .stateMap)
  with () ← ≡inj₂
... | yes refl
  rewrite pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap)
  with refl ← ≡inj₂
  =  LocalStepSound menv ls′ st
sliceComplete (DishonestLocalStep _ _) ()
sliceComplete (WaitUntil t allt <t) refl = WaitUntilSound t <t allt
sliceComplete {s = s} (Deliver {(_ , p′ , m)} tpm∈) ≡inj₂
  with p ≟ p′
... | yes refl
  rewrite (sym $ deliverMsg-slice s m tpm∈)
  with refl ← ≡inj₂
  = DeliverSound m tpm∈
... | no p≢
  with honest? p′
... | no ¬hp′ with () ← ≡inj₂
... | yes hp′ with () ← ≡inj₂


-- for any valid slice step there is a corresponding global step
sliceSound : ∀ s {slstep :  ss′ ←—ᴸ sliceState s} → SliceValidStep s slstep
  → ∃ λ s′ → (s′ ¹←— s) × ss′ ≡ sliceState s′
sliceSound s (LocalStepSound menv ls′ st) =
  let s′ = broadcast (s .currentTime) menv (s ＠ p ≔ ls′)
  in s′
   , LocalStep st
   , cong (λ ◆ → mkSliceState _ ◆ _) (sym $ pLookup∘updateAt p ⦃ hp ⦄ {const ls′} (s .stateMap))
sliceSound s (DeliverSound m tpm∈) =
 let s′ = deliverMsg s tpm∈
 in s′
  , Deliver tpm∈
  , cong₂ (mkSliceState (s .currentTime)) (deliverMsg-slice s m tpm∈) refl
sliceSound s (WaitUntilSound t <t allt) =
 let s′ = record s { currentTime = t }
 in s′ , WaitUntil t allt <t , refl
