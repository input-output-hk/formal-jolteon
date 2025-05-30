module DummyHashing where

open import Prelude
open import Agda.Builtin.Equality.Erase

record DummyHash : Type where
  constructor #_
  field value : ℕ

open import Hash DummyHash

private variable A B : Type

postulate
  unsafePostulatedInjectivity : {f : A → B} {x y : A} → f x ≡ f y → x ≡ y

private
  -- We match a lot on equality proofs at compile time, so we don't want
  -- evaluate decidability proofs using unary arithmetic. Using `primEraseEquality`
  -- lets us avoid this.
  eraseDecEq : ∀ {x y : A} → Dec (x ≡ y) → Dec (x ≡ y)
  eraseDecEq (yes eq) = yes (primEraseEquality eq)
  eraseDecEq (no neq) = no neq

instance
  DecEq-DummyHash : DecEq DummyHash
  DecEq-DummyHash ._≟_ (# a) (# b) = eraseDecEq (mapDec (λ {refl → refl}) (λ {refl → refl}) (a ≟ b))

  Monoid-DummyHash : Monoid DummyHash
  Monoid-DummyHash .ε               = # 0
  Monoid-DummyHash ._◇_ (# 0) (# b) = # b
  Monoid-DummyHash ._◇_ (# a) (# 0) = # a
  Monoid-DummyHash ._◇_ (# a) (# b) = # (7 * a + 13 * b)

DummyHashing : HashAssumptions
DummyHashing = record {go}
  where module go where

  instance
    Digestable-ℕ   = Digestable ℕ          ∋ λ where .digest     → #_
                                                     .digest-inj → unsafePostulatedInjectivity
    Digestable-ℕ×ℕ = Digestable (ℕ × ℕ)    ∋ λ where .digest (n , m) → digest n ◇ digest m
                                                     .digest-inj → unsafePostulatedInjectivity
    Digestable-H×ℕ = Digestable (Hash × ℕ) ∋ λ where .digest (h , n) → digest h ◇ digest n
                                                     .digest-inj → unsafePostulatedInjectivity

  hash     = id
  hash-inj = id

DummySigning : (PublicKey → Signature → Hash → Bool) → SignatureAssumptions
DummySigning versig = record {go} where module go where
  open HashAssumptions DummyHashing

  verify-signature = versig

  sign : ∀ {A} → ⦃ Digestable A ⦄ → Key → A → Signature
  sign k a = k ♯ ◇ a ♯
