{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.State.Messages (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Properties.Core ⋯

open L.Mem

-- ** lemmas about receiveMsg (i.e. the Deliver rule)

receiveMsg-ls≡ : ∀ ⦃ _ : Honest p ⦄ {s} mhm →
  let s' = receiveMsg s mhm in
  (s' ＠ᵐ p) ≡ record (s ＠ᵐ p) {inbox = (s' ＠ᵐ p) .inbox}
receiveMsg-ls≡ nothing = refl
receiveMsg-ls≡ {p} ⦃ hp ⦄ {s} (just ((p′ ,· hp′) , m))
  with p ≟ p′
... | yes refl
  rewrite pLookup∘updateAt p {receiveMessage m} s
  = refl
... | no p≢
  rewrite pLookup∘updateAt′ p p′ ⦃ toRelevant hp′ ⦄ {receiveMessage m} (p≢ ∘ ↑-injective) s
  = refl

module _ {p} ⦃ _ : Honest p ⦄ {s} mhm (let ls≡ = receiveMsg-ls≡ {p}{s} mhm) where
  receiveMsg-db     = cong db ls≡
  receiveMsg-tcLast = cong tc-last ls≡
  receiveMsg-rCur   = cong r-cur ls≡
  receiveMsg-qcHigh = cong qc-high ls≡
  receiveMsg-phase  = cong phase ls≡
  receiveMsg-roundA = cong roundAdvanced? ls≡
  receiveMsg-final  = cong finalChain ls≡

-- ** lemmas about broadcasts (i.e. the LocalStep rule)

expandBroadcasts-message :
  (t′ , p , m) ∈ expandBroadcasts t env
  ─────────────────────────────────────
  m ≡ env ∙message
expandBroadcasts-message {t = t}{[ _m ⟩} tpm∈
  with _ , _ , refl ← ∈-map⁻ (λ p → (t , p , _m)) tpm∈
  = refl
expandBroadcasts-message {env = [ _ ∣ _m ⟩} (here refl) = refl
