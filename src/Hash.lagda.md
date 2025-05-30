<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude

module Hash (ByteString : Type)
            ⦃ _ : DecEq ByteString ⦄
            ⦃ _ : Monoid ByteString ⦄ where

private variable A B : Type
```
-->

# Hashes

Hashes are represented as bitstrings:
```agda
Digest Hash : Type
Digest = ByteString
Hash   = ByteString
```
<!--
```agda
variable H H′ : Hash
```
-->

Digestable types are collected under a appropriate typeclass:
```agda
record Digestable (A : Type) : Type where
  field digest     : A → Digest
        digest-inj : Injective≡ digest
```
<!--
```agda
open Digestable ⦃...⦄ public

Digestable¹ : ∀ {A} → (A → Type) → Type
Digestable¹ P = ∀ {x} → Digestable (P x)

instance
  Digestable-Hash : Digestable Hash
  Digestable-Hash = λ where
    .digest → id
    .digest-inj → id
```
-->

We assume an injective hash function and ways to digest base types:
```agda
record HashAssumptions : Type₁ where
  field
    -- how to digest base types
    instance
      Digestable-ℕ   : Digestable ℕ
      Digestable-ℕ×ℕ : Digestable (ℕ × ℕ)
      Digestable-H×ℕ : Digestable (Hash × ℕ)

    -- agreed-upon hash function (e.g. SHA256)
    hash     : Digest → Hash
    hash-inj : Injective≡ hash

  infix 100 _♯
  _♯ : ⦃ Digestable A ⦄ → A → Hash
  _♯ = hash ∘ digest

  ♯-inj : ⦃ _ : Digestable A ⦄ → Injective≡ {A = A} _♯
  ♯-inj = digest-inj ∘ hash-inj
```

# Signatures

Let's start with various aliases for bitstrings and key pairs:
```agda
Key Signature PublicKey PrivateKey : Type
Key        = ByteString
Signature  = ByteString
PublicKey  = Key
PrivateKey = Key

record KeyPair : Type where
  constructor mk-keyPair
  field publicKey  : PublicKey
        privateKey : PrivateKey
open KeyPair public
```

We then assume that there is a way to sign (hashable) values,
as well as the existence of a suitable signature verification algorithm (e.g. SHA256).
```agda
record SignatureAssumptions : Type₁ where
  field
    verify-signature : PublicKey → Signature → Hash → Bool
    sign : ⦃ Digestable A ⦄ → Key → A → Signature
```
