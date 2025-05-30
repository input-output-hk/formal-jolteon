{-# OPTIONS --safe #-}
module Jolteon.Global.TraceVerification.ToSpec where

open import Prelude
open import Prelude.Result

record ToSpec (T S : Type) (E : T → Type) : Type where
  field
    fromSpec : S → T
    toSpec   : (t : T) → Result (E t) (∃[ s ] fromSpec s ≡ t)

open ToSpec ⦃ ... ⦄ public

IdToSpec : ∀ {A E} → ToSpec A A E
IdToSpec .fromSpec = id
IdToSpec .toSpec t = Ok (t , refl)

findInList : {A : Type}
           → (xs : List A)
           → (P : A → Type)
           → ⦃ P ⁇¹ ⦄
           → Result ⊤ (∃[ x ] x ∈ xs × P x)
findInList [] P = Err _
findInList (x ∷ xs) P = (do
    px ← ¿ P x ¿ᴿ: λ _ → tt
    return (x , here refl , px))
  catch λ _ → do
    y , y∈xs , py ← findInList xs P
    return (y , there y∈xs , py)

private variable
  A B : Type

TodoErr : A → Type
TodoErr _ = ⊤

instance
  ToSpecList : ⦃ ToSpec A B TodoErr ⦄ → ToSpec (List A) (List B) TodoErr
  ToSpecList .fromSpec = map fromSpec
  ToSpecList .toSpec [] = return ([] , refl)
  ToSpecList .toSpec (x ∷ xs) = do
    y  , refl ← toSpec x
    let work = toSpec xs
    ys , refl ← work
    return (y ∷ ys , refl)

  ToSpecMaybe : ⦃ ToSpec A B TodoErr ⦄ → ToSpec (Maybe A) (Maybe B) TodoErr
  ToSpecMaybe .fromSpec = M.map fromSpec
  ToSpecMaybe .toSpec nothing = return (nothing , refl)
  ToSpecMaybe .toSpec (just x) = do
    y , refl ← toSpec x
    return (just y , refl)

  ToSpecPair : ∀ {A₁ A₂ B₁ B₂}
             → ⦃ ToSpec A₁ B₁ TodoErr ⦄
             → ⦃ ToSpec A₂ B₂ TodoErr ⦄
             → ToSpec (A₁ × A₂) (B₁ × B₂) TodoErr
  ToSpecPair .fromSpec (x , y) = fromSpec x , fromSpec y
  ToSpecPair .toSpec (x , y) = do
    x , refl ← toSpec x
    y , refl ← toSpec y
    return ((x , y) , refl)
