{-# OPTIONS --safe #-}
module Prelude.Monoid where

open import Prelude.Init

record Monoid (A : Type) : Type where
  field ε : A
        _◇_ : A → A → A
  infixr 6 _◇_
open Monoid ⦃...⦄ public

private variable A : Type

instance
  Monoid-List : Monoid (List A)
  Monoid-List .ε = []
  Monoid-List ._◇_ = _++_

  Monoid-Bin : Monoid Bitstring
  Monoid-Bin .ε = Bin.zero
  Monoid-Bin ._◇_ = Bin._+_
