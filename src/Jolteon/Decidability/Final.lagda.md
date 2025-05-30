<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Decidability.Final (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Decidability.VoteSharesOf ⋯
open import Jolteon.Decidability.HighestQC ⋯
```
-->

```agda
allValidChainsUpToLength : ℕ → Messages → List Chain
allValidChainsUpToLength zero ms = [ [] ]
allValidChainsUpToLength (suc n) ms =
  let
    vs = allValidChainsUpToLength n ms
    -- bs is the list of blocks for the current length
    bs = filter (λ b → ¿ b ∙round ≡ suc n ¿) (allBlocks ms)
    -- We dont't need to check `b .blockQC ∙∈ ms` since this is implied by
    -- b coming from a Propose b message (i,e. b .blockQC will always be a received QC).

    f : Chain → List Chain
    f ch = bs >>= (λ b → if ⌊ ¿ b -connects-to- ch ¿ ⌋ then [ b ∷ ch ] else [])
  in
    vs ++ (vs >>= f)
-- We construct chains round by round in order to not assume any particular order in the list of messages.

maxRound : Messages → Round
maxRound ms = L.Ex.max 0 (L.map _∙round (allBlocks ms))

allValidChains : Messages → List Chain
allValidChains ms = allValidChainsUpToLength (maxRound ms) ms

chain-∈⇒allValidChainsUpToLength : ∀ (n : ℕ) →
  ∙ ch ∙round ≤ n
  ∙ ch ∙∈ ms
    ──────────────────────────────────
    ch ∈ allValidChainsUpToLength n ms
chain-∈⇒allValidChainsUpToLength zero r≤n [] = here refl
chain-∈⇒allValidChainsUpToLength zero r≤n (_ ∷ _ ⊣ connects∶ _ _ r>)
  = ⊥-elim (Nat.n≮0 (Nat.≤-trans r> r≤n))
chain-∈⇒allValidChainsUpToLength (suc n) r≤n []
  = L.Mem.∈-++⁺ˡ (chain-∈⇒allValidChainsUpToLength n Nat.z≤n [])
chain-∈⇒allValidChainsUpToLength {b ∷ ch} {ms} (suc n) r≤n (b∈ ∷ ch∈ ⊣ x)
  with b ∙round Nat.≤? n
... | yes br≤n
  = L.Mem.∈-++⁺ˡ (chain-∈⇒allValidChainsUpToLength {b ∷ ch} n br≤n (b∈ ∷ ch∈ ⊣ x))
... | no br≰n
  with eq ← b ∙round ≡ suc n ∋ Nat.≤∧≮⇒≡ r≤n (br≰n ∘ Nat.s≤s⁻¹) =
  let
    open Nat
    connects∶ _ r≡ ir = x
    chr≤n : (ch ∙round) ≤ n
    chr≤n = s≤s⁻¹ (≤-trans (≤-trans (s≤s (≤-reflexive (sym r≡))) ir) r≤n)

    ch∈all : ch ∈ allValidChainsUpToLength n ms
    ch∈all = chain-∈⇒allValidChainsUpToLength n chr≤n ch∈

    vs = allValidChainsUpToLength n ms

    bs = filter (λ b → ¿ b ∙round ≡ suc n ¿) (allBlocks ms)

    f    : Chain → List Chain
    f ch = L.concatMap (λ b → if ⌊ ¿ b -connects-to- ch ¿ ⌋ then [ b ∷ ch ] else []) bs

    b∈bs : b ∈ bs
    b∈bs = L.Mem.∈-filter⁺ _ b∈ eq

  in
    L.Mem.∈-++⁺ʳ vs
  $ L.Mem.>>=-∈↔ .Inverse.to
      ( ch
      , ch∈all
      , L.Mem.>>=-∈↔ .Inverse.to (b , b∈bs , subst (λ c → _ ∈ (if ⌊ c ⌋ then _ else _))
                                                   (sym $ proj₂ $ dec-✓ x)
                                                   (here refl)))

maxRound-correct : ch ∙∈ ms → ch ∙round ≤ maxRound ms
maxRound-correct [] = Nat.z≤n
maxRound-correct {b ∷ ch}{ms} (b∈ ∷ ch∈ ⊣ _) =
  let
    es = map (_∙round) (allBlocks ms)

    be∈ : b ∙round ∈ es
    be∈ = L.Mem.∈-map⁺ _∙round b∈
  in
    L.All.lookup {P = _≤ maxRound ms} (L.Ex.xs≤max 0 es) be∈

chain-∈⇒allValidChains : ch ∙∈ ms → ch ∈ allValidChains ms
chain-∈⇒allValidChains {ms = ms} ch∈ =
  chain-∈⇒allValidChainsUpToLength (maxRound ms) (maxRound-correct ch∈) ch∈
```

### Decidability of certified-∈ / final-∈ / longer-final-∈

```agda
instance
  Dec-certified-∈ : _-certified-∈-_ ⁇²
  Dec-certified-∈ {b} {ms} .dec
    with ¿ Any (λ qc → (qc ∙blockId ≡ b ∙blockId) × (qc ∙round   ≡ b ∙round)) (allQCs ms) ¿
  ... | yes q = let (qc , qc∈all , (eqᵢ , eqᵣ)) = L.Mem.find q in
    yes $ certified (allQCs-sound ms qc∈all) eqᵢ eqᵣ
  ... | no ¬q = no λ where
    (certified {qc} qc∈ refl refl) →
      ¬q $ L.Any.map (λ x → cong proj₁ (sym x) , cong proj₂ (sym x)) (L.Any.map⁻ $ allQCs-complete ms qc∈)

  Dec-final-∈ : ∀ {b ch ms} → (b ∶ ch final-∈ ms) ⁇
  Dec-final-∈ {b′} {ch} {ms} .dec with ch
  ... | [] = no λ ()
  ... | (b ∷ ch) with ¿ b -certified-∈- ms ¿
  ... | no ¬bcert = no λ where (final∈ bcert _ _ _) → ¬bcert bcert
  ... | yes bcert with ¿ b′ -certified-∈- ms ¿
  ... | no ¬b′cert = no λ where (final∈ _ b′cert _ _) → ¬b′cert b′cert
  ... | yes b′cert with ¿ (b′ ∷ b ∷ ch) ∙∈ ms ¿
  ... | no ch∉ =  no λ where (final∈ _ _ ch∈ _) → ch∉ ch∈
  ... | yes ch∈ with ¿ b′ ∙round ≡ 1 + b ∙round ¿
  ... | no ¬bsuc = no λ where (final∈ _ _ _ bsuc) → ¬bsuc bsuc
  ... | yes bsuc = yes (final∈ bcert b′cert ch∈ bsuc)

  Dec-longer-final-∈ : _longer-final-∈_ ⁇²
  Dec-longer-final-∈ {b}{ls} .dec
    with ¿ Any (λ ch → b ∶ ch longer-final-∈ ls) (allValidChains (ls .db)) ¿
  ... | yes ch∈ = let (_ , p) = L.Any.satisfied ch∈ in yes (mk p)
  ... | no  ∄ch = no λ where
    (mk {ch = ch} lf@(final∈ _ _ bch∈ _ , _)) →
      let
        ch∈all : ch ∈ allValidChains (ls .db)
        ch∈all = chain-∈⇒allValidChains (chain-∈-tail bch∈)
      in ∄ch $ L.Any.map (λ where refl → lf) ch∈all

  Dec-connects-∈ : _-connects-∈-_ ⁇²
  Dec-connects-∈ {b} {ms} .dec
    with ¿ Any (λ ch → (ch ∙∈ ms) × (b -connects-to- ch)) (allValidChains ms) ¿
  ... | no ¬p = no λ where
    (mk {ch = ch} ch∈ b←) →
      ¬p (L.Any.map (λ where refl → ch∈ , b←) (chain-∈⇒allValidChains ch∈))
  ... | yes p
    with _ , ch∈ , b← ← L.Any.satisfied p
    = yes $ mk ch∈ b←

_ = Decidable² _-highest-qc-∈-_
  ∋ dec²

_ = Decidable² _-certified-∈-_
  ∋ dec²

_ : ∀ {b ch ms} → Dec (b ∶ ch longer-final-∈ ms)
_ = dec

_ : Decidable² _longer-final-∈_
_ = dec²

_ : Decidable² _-connects-∈-_
_ = dec²
```
