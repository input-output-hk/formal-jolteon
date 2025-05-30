-- Assumptions used at runtime when verifying traces from "real" nodes.
module Jolteon.Global.TraceVerification.Assumptions where

open import Prelude
open import Relation.Nullary.Decidable.Core

open import Jolteon.Base
open import Jolteon.Assumptions

open import Agda.Builtin.TrustMe using (primTrustMe)

-- Runtime checks ---

private postulate
  error : {A : Type} → String → A
{-# COMPILE GHC error = \ _ -> error . Data.Text.unpack #-}

runtimeCheck : {A : Type} → ⦃ A ⁇ ⦄ → String → A
runtimeCheck {A} err with ¿ A ¿
... | yes a = a
... | no _  = error err

-- Byte strings ---

postulate
  ByteString : Type

{-# FOREIGN GHC import Data.ByteString #-}
{-# COMPILE GHC ByteString = type ByteString #-}

private postulate
    eqByteString     : ByteString → ByteString → Bool
    emptyByteString  : ByteString
    appendByteString : ByteString → ByteString → ByteString

instance
  Monoid-ByteString : Monoid ByteString
  Monoid-ByteString .ε   = emptyByteString
  Monoid-ByteString ._◇_ = appendByteString

{-# COMPILE GHC eqByteString = (==) #-}
{-# COMPILE GHC emptyByteString = mempty #-}
{-# COMPILE GHC appendByteString = (<>) #-}

instance
  DecEq-ByteString : DecEq ByteString
  DecEq-ByteString ._≟_ a b =
    if eqByteString a b
    then yes primTrustMe
    else no (λ { refl → error "impossible: eqByteString" })

-- Hashing ---

{-# FOREIGN GHC import Data.ByteString.Builder (toLazyByteString, word64LE) #-}

open import Agda.Builtin.Word
open import Hash ByteString

{-# FOREIGN GHC import qualified Crypto.Hash.SHA512 #-}

postulate
  sha512   : ByteString → ByteString
  word64LE : Word64 → ByteString

{-# COMPILE GHC sha512   = Crypto.Hash.SHA512.hash #-}
{-# COMPILE GHC word64LE = toStrict . toLazyByteString . word64LE #-}

instance
  Digest-Word : Digestable Word64
  Digest-Word .digest     = word64LE
  Digest-Word .digest-inj = error "digest-inj-Word64"

Digest-ℕ : Digestable ℕ
Digest-ℕ .digest n = digest (primWord64FromNat n)
Digest-ℕ .digest-inj = error "digest-inj-ℕ"

Digest-Hash : Digestable Hash
Digest-Hash .digest = id
Digest-Hash .digest-inj eq = eq

infixr 6 _⨂_
_⨂_ : {A B : Type} → Digestable A → Digestable B → Digestable (A × B)
(dA ⨂ dB) .digest (x , y) = dA .Digestable.digest x ◇ dB .Digestable.digest y
(dA ⨂ dB) .digest-inj = error "digest-inj-⨂"

infix 9 _＊ _？
_＊ : {A : Type} → Digestable A → Digestable (List A)
(dA ＊) .digest = L.foldl (λ b x → b ◇ dA .Digestable.digest x) ε
(dA ＊) .digest-inj = error "digest-inj-＊"

_？ : {A : Type} → Digestable A → Digestable (Maybe A)
(dA ？) .digest nothing = ε
(dA ？) .digest (just x) = dA .Digestable.digest x
(dA ？) .digest-inj = error "digest-inj-?"

-- Signatures ---

{-# FOREIGN GHC import Crypto.Sign.Ed25519 (dverify, dsign, PublicKey(..), SecretKey(..), Signature(..)) #-}
postulate
  dverifyEd25519 : PublicKey → ByteString → Signature → Bool
  dsignEd25519   : PrivateKey → ByteString → Signature
{-# COMPILE GHC dverifyEd25519 = \ key msg sig -> dverify (PublicKey key) msg (Signature sig) #-}
{-# COMPILE GHC dsignEd25519   = \ key msg -> unSignature (dsign (SecretKey key) msg) #-}

-- Runtime assumptions ---

record RuntimeNode : Type where
  field
    isHonest : Bool
    keyPair  : KeyPair

open RuntimeNode

record RuntimeParams : Type where
  field
    {n}         : ℕ
    nodes       : Vec RuntimeNode (suc n)
    τ Δ         : Time
    roundLeader : Round → PublicKey

unsafeLookupKey : ∀ {n} → Vec RuntimeNode n → PublicKey → Fin n
unsafeLookupKey [] key = error "Unknown public key!"
unsafeLookupKey (node ∷ nodes) key =
  if node .keyPair .publicKey == key
  then fzero
  else fsuc (unsafeLookupKey nodes key)

⋯ : RuntimeParams → Assumptions
⋯ params = record { Impl
                  ; noHashCollision = λ {b ch} → Impl.noHashCollision {b} {ch}
                  }
  where module Impl where
    module P = RuntimeParams params

    hashes : HashAssumptions
    hashes .HashAssumptions.Digestable-ℕ   = Digest-ℕ
    hashes .HashAssumptions.Digestable-ℕ×ℕ = Digest-ℕ ⨂ Digest-ℕ
    hashes .HashAssumptions.Digestable-H×ℕ = Digest-Hash ⨂ Digest-ℕ
    hashes .HashAssumptions.hash = sha512
    hashes .HashAssumptions.hash-inj = error "hash-inj"

    open HashAssumptions hashes

    signatures : SignatureAssumptions
    signatures .SignatureAssumptions.verify-signature key sig msg = dverifyEd25519 key msg sig
    signatures .SignatureAssumptions.sign key x = dsignEd25519 key (digest x)

    nodes : ℕ
    nodes = suc P.n

    Pid = Fin nodes

    nodes⁺ : nodes > 0
    nodes⁺ = Nat.s≤s Nat.z≤n

    τ : Time
    τ = P.τ

    Δ : Time
    Δ = P.Δ

    roundLeader : Round → Pid
    roundLeader = unsafeLookupKey P.nodes ∘ P.roundLeader

    Honest : Pid → Type
    Honest p = V.lookup P.nodes p .isHonest ≡ true

    Dec-Honest : Honest ⁇¹
    Dec-Honest = it

    honest-majority : _
    honest-majority = runtimeCheck "No honest majority!"

    -- We can identify transactions with their hashes.
    Transaction : Type
    Transaction = Hash

    DecEq-Tx : DecEq Transaction
    DecEq-Tx = it

    Transactions = List Transaction
    PayloadQC    = Hash × Round × List Pid
    PayloadTC    = Round × List (Pid × PayloadQC)
    PayloadBlock = PayloadQC × Maybe PayloadTC × Round × Transactions
    PayloadChain = List PayloadBlock

    instance
      Digestable-Pid : Digestable Pid
      Digestable-Pid .digest p = digest (V.lookup P.nodes p .keyPair .publicKey)
      Digestable-Pid .digest-inj = error "digest-inj-Pid"

    -- TODO: These should be part of the spec!
    -- TODO: These implementations don't align with the Rust PoC implementation
    --       (see jolteon-poc/jolteon/src/jolteon/types.rs)
    instance
      Digestable-Txs : Digestable Transactions
      Digestable-Txs = it ＊

      Digestable-QCᴾ : Digestable PayloadQC
      Digestable-QCᴾ = it ⨂ it ⨂ it ＊

      Digestable-ℕ×QCᴾ : Digestable (ℕ × PayloadQC)
      Digestable-ℕ×QCᴾ = it ⨂ it

      Digestable-TCᴾ : Digestable PayloadTC
      Digestable-TCᴾ = it ⨂ (it ⨂ it) ＊

      Digestable-Blockᴾ : Digestable PayloadBlock
      Digestable-Blockᴾ = it ⨂ it ？ ⨂ it ⨂ it

      Digestable-Chainᴾ : Digestable PayloadChain
      Digestable-Chainᴾ = it ＊

    noHashCollision : ∀ {b : PayloadBlock} {ch : PayloadChain} →
      let instance _ = Digestable-Blockᴾ
                   _ = Digestable-Chainᴾ
      in ch ♯ ≢ b ♯
    noHashCollision = error "noHashCollision"

    keys : Pid → KeyPair
    keys p = V.lookup P.nodes p .keyPair
