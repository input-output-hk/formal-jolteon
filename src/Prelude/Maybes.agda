{-# OPTIONS --safe #-}
open import Prelude.Init

module Prelude.Maybes where

private variable A : Type

open M

Any-just : ∀ {x : A} {mx : Maybe A} {P : A → Type}
 → mx ≡ just x
 → M.Any.Any P mx
 → P x
Any-just refl (M.Any.just p) = p

Any⇒Is-just : ∀ {mx : Maybe A} {P : A → Type}
 → M.Any.Any P mx
 → Is-just mx
Any⇒Is-just {mx = .(just _)} (M.Any.just _) = M.Any.just tt

module _ {A : Type ℓ} where
  is-just≡ : ∀ {mx : Maybe A} → T (M.is-just mx) → ∃ λ x → mx ≡ just x
  is-just≡ {mx = just _} _ = -, refl

  ¬is-just≡ : ∀ {mx : Maybe A} → ¬ T (M.is-just mx) → mx ≡ nothing
  ¬is-just≡ {mx = just _}  p = ⊥-elim $ p tt
  ¬is-just≡ {mx = nothing} _ = refl

  Is-just? : (mx : Maybe A) → Dec (Is-just mx)
  Is-just? = M.Any.dec λ _ → yes tt

  Is-just⇒≢nothing : ∀ {mx : Maybe A} → Is-just mx → mx ≢ nothing
  Is-just⇒≢nothing {mx = nothing} () _
  Is-just⇒≢nothing {mx = just _} _ ()

  Is-nothing≡ : ∀ {mx : Maybe A} → Is-nothing mx → mx ≡ nothing
  Is-nothing≡ {mx = nothing} _ = refl
  Is-nothing≡ {mx = just _} (M.All.just ())

  ¬Is-just⇒Is-nothing : ∀ {mx : Maybe A} → ¬ Is-just mx → Is-nothing mx
  ¬Is-just⇒Is-nothing {mx = nothing} _ = M.All.nothing
  ¬Is-just⇒Is-nothing {mx = just _}  p = ⊥-elim $ p (M.Any.just tt)

  destruct-Is-just : ∀ {mx : Maybe A}
    → Is-just mx
    → ∃ λ x → mx ≡ just x
  destruct-Is-just {mx = nothing} ()
  destruct-Is-just {mx = just _}  _ = _ , refl

  MAll⇒¬MAny : ∀ {m : Maybe A} → M.All.All (const ⊥) m → ¬ M.Any.Any (const ⊤) m
  MAll⇒¬MAny {m = nothing} M.All.nothing ()

  mk-Is-just : ∀ {mx : Maybe A} {x : A} → mx ≡ just x → Is-just mx
  mk-Is-just refl = M.Any.just tt

destruct-Any-just : ∀ {mx : Maybe A} {P : A → Type}
 → M.Any.Any P mx
 → ∃ λ x → mx ≡ just x × P x
destruct-Any-just ∃p =
  let x , x≡ = destruct-Is-just (Any⇒Is-just ∃p)
  in  x , x≡ , Any-just x≡ ∃p
