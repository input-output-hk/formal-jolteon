## Assumptions of the Jolteon protocol

<!--
```agda
{-# OPTIONS --safe #-}
module Jolteon.Assumptions where

open import Prelude
import Hash

open import Jolteon.Base
```
-->

```agda
record Assumptions : Type₁ where

  -- * cryptographic assumptions
  field ByteString : Type
        ⦃ DecEq-ByteString ⦄ : DecEq ByteString
        ⦃ Monoid-ByteString ⦄ : Monoid ByteString

  open Hash ByteString public

  field hashes : _
  open HashAssumptions hashes public

  field signatures : _
  open SignatureAssumptions signatures public

  -- * participants

  field nodes  : ℕ -- Fixed number of participants.
        nodes⁺ : nodes > 0

  Pid : Type
  Pid = Fin nodes -- Each participant is assigned an identifier `Pid`.

  allPids : List Pid
  allPids = L.allFin nodes

  lengthAllPids : length allPids ≡ nodes
  lengthAllPids = L.length-tabulate id

  allPids-complete : ∀ (xs : List Pid) → xs ⊆ˢ allPids
  allPids-complete xs {x} x∈ = L.Mem.∈-allFin x

  -- * timer duration

  field τ Δ : Time

  -- * leader selection (TODO : How is it done?)

  field roundLeader : Round → Pid

  -- * honest majority
  -- TODO: Express ratios also in terms of f and prove equivalence.
  -- f < 1 /3 * n

  -- used for certificates
  IsMajorityRatio = λ n → 3 * n ≥ 2 * nodes

  -- used for honest processes
  IsMajorityRatio⁺ = λ n → 3 * n > 2 * nodes

  -- used for global direct-commit
  IsMoreThanFRatio = λ n → 3 * n > nodes

  -- used for timeouts
  IncludesHonestRatio = IsMoreThanFRatio

  IsMajority : ∀ {A : Type} → List A → Type
  IsMajority = IsMajorityRatio  ∘ length

  IsMajority⁺ : ∀ {A : Type} → List A → Type
  IsMajority⁺ = IsMajorityRatio⁺ ∘ length

  MoreThanF : ∀ {A : Type} → List A → Type
  MoreThanF = IsMoreThanFRatio ∘ length

  IncludesHonest : ∀ {A : Type} → List A → Type
  IncludesHonest = IncludesHonestRatio ∘ length

  nodesMajority : IsMajorityRatio nodes
  nodesMajority = Nat.m≤n+m _ nodes

  allPidsMajority : IsMajority allPids
  allPidsMajority = subst IsMajorityRatio (sym lengthAllPids) nodesMajority

  field Honest : Pid → Type
        instance Dec-Honest : Honest ⁇¹

  Dishonest = ¬_ ∘ Honest

  honest? : Decidable¹ Honest
  honest? = dec¹ ⦃ Dec-Honest ⦄

  isHonest : Pid → Bool
  isHonest p = ⌊ honest? p ⌋

  field honest-majority : IsMajority⁺ (filter honest? allPids)

  dishonest? : Decidable¹ Dishonest
  dishonest? = ¬? ∘ honest?

  -- f < 1/3 * nodes
  dishonestMinority : 3 * length (filter dishonest? allPids) < nodes
  dishonestMinority =
    let ds = length (filter dishonest? allPids)
        hs = length (filter honest? allPids)

        open Nat ; open ≤-Reasoning
    in
    begin-strict
      3 * ds
    ≡⟨⟩
      ds + 2 * ds
    <⟨ +-monoʳ-< ds (+-cancelˡ-< (2 * hs) (2 * ds) hs (
       begin-strict
         2 * hs + 2 * ds
       ≡⟨ (sym $ *-distribˡ-+ 2 hs ds) ⟩
         2 * (hs + ds)
       ≡⟨ cong (2 *_) $ sym $ filter-length honest? {allPids} ⟩
         2 * length allPids
       ≡⟨ cong (2 *_) lengthAllPids ⟩
         2 * nodes
       <⟨ honest-majority ⟩
        3 * hs
       ≡⟨ +-comm hs (2 * hs) ⟩
         2 * hs + hs
       ∎
       ))⟩
      ds + hs
    ≡⟨ +-comm ds hs ⟩
      hs + ds
    ≡⟨ sym $ filter-length honest? {allPids} ⟩
     length allPids
     ≡⟨ lengthAllPids ⟩
      nodes
    ∎


  -- * abstract type of transactions

  field
    Transaction : Type
    instance DecEq-Tx : DecEq Transaction

  Transactions = List Transaction

  -- * digesting payloads

  PayloadQC    = Hash × Round × List Pid
  PayloadTC    = Round × List (Pid × PayloadQC)
  PayloadBlock = PayloadQC × Maybe PayloadTC × Round × Transactions
  PayloadChain = List PayloadBlock

  field
    instance
      Digestable-Txs    : Digestable Transactions
      Digestable-QCᴾ    : Digestable PayloadQC
      Digestable-ℕ×QCᴾ  : Digestable (ℕ × PayloadQC)
      Digestable-TCᴾ    : Digestable PayloadTC
      Digestable-Blockᴾ : Digestable PayloadBlock
      Digestable-Chainᴾ : Digestable PayloadChain

    -- no chain should have the same hash as a block
    noHashCollision : ∀ {b : PayloadBlock} {ch : PayloadChain} →
      let instance _ = Digestable-Blockᴾ; _ = Digestable-Chainᴾ in
      ch ♯ ≢ b ♯

  noHashCollision˘ : ∀ {b : PayloadBlock} {ch : PayloadChain} →
    let instance _ = Digestable-Blockᴾ; _ = Digestable-Chainᴾ in
    b ♯ ≢ ch ♯
  noHashCollision˘ = Eq.≢-sym noHashCollision

  -- * public-key infrastructure

  field keys      : Pid → KeyPair

  _∙pk : Pid → PublicKey
  p ∙pk = keys p .publicKey

  _∙sk : Pid → PrivateKey
  p ∙sk = keys p .privateKey

  lookupKey : (pk : PublicKey) → Dec (∃[ p ] p ∙pk ≡ pk)
  lookupKey pk = case go allPids of λ where
      (yes (p , eq , _)) → yes (p , eq)
      (no notfound)      → no (λ (p , eq) → notfound (p , eq , allPids-complete (p ∷ []) (here refl)))
    where
      go : (ps : List Pid) → Dec (∃[ p ] p ∙pk ≡ pk × p ∈ ps)
      go [] = no λ ()
      go (p ∷ ps) with p ∙pk ≟ pk
      ... | yes refl = yes (p , refl , here refl)
      ... | no neq with go ps
      ...   | yes (p , eq , p∈) = yes (p , eq , there p∈)
      ...   | no notfound       = no λ where
        (p , eq , here refl) → neq eq
        (p , eq , there p∈)  → notfound (p , eq , p∈)

  -- * extra lemmas

  open Nat; open ≤-Reasoning

  majority⁺ : ¬ IsMajorityRatio 0
  majority⁺ _ with nodes | nodes⁺
  ... | 0 | ()

  moreThanF⁺ : ¬ IsMoreThanFRatio 0
  moreThanF⁺ _ with nodes | nodes⁺
  ... | 0 | ()

  majority-≤ : ∀ {n m} →
    ∙ n ≤ m
    ∙ IsMajorityRatio n
      ─────────────────
      IsMajorityRatio m
  majority-≤ {n}{m} n≤m maj = begin
    2 * nodes ≤⟨ maj ⟩
    3 * n     ≤⟨ *-mono-≤ {3} ≤-refl n≤m ⟩
    3 * m     ∎ where open Nat; open ≤-Reasoning

  honest-≤ : ∀ {n m} →
    ∙ n ≤ m
    ∙ IncludesHonestRatio n
      ─────────────────────
      IncludesHonestRatio m
  honest-≤ {n}{m} n≤m maj = begin-strict
    nodes <⟨ maj ⟩
    3 * n ≤⟨ *-mono-≤ {3} ≤-refl n≤m ⟩
    3 * m ∎ where open Nat; open ≤-Reasoning

  majority-∷ : ∀ {n} → IsMajorityRatio n → IsMajorityRatio (suc n)
  majority-∷ = majority-≤ (Nat.n≤1+n _)

  honest-∷ : ∀ {n} → IncludesHonestRatio n → IncludesHonestRatio (suc n)
  honest-∷ = honest-≤ (Nat.n≤1+n _)

  majority-⊆ : ∀ {A : Type} {vs vs′ : List A} →
    ∙ vs ⊆ vs′
    ∙ IsMajority vs
      ──────────────
      IsMajority vs′
  majority-⊆ = majority-≤ ∘ L.SubL.length-mono-≤

  honest-⊆ : ∀ {A : Type} {vs vs′ : List A} →
    ∙ vs ⊆ vs′
    ∙ IncludesHonest vs
      ──────────────────
      IncludesHonest vs′
  honest-⊆ = honest-≤ ∘ L.SubL.length-mono-≤

  honestFromThird : ∀ {pids} →
    ∙ Unique pids
    ∙ 3 * length pids ≥ nodes
      ───────────────────────
      Any Honest pids
  honestFromThird {xs} uxs xs≥n/3 = QED
    where
    hs = filter honest? allPids

    uhs : Unique hs
    uhs = filter⁺ honest? (allFin⁺ nodes)
      where open L.Unique

    xs∩ = xs ∩ hs

    len+ : length xs + length hs > nodes
    len+ = *-cancelˡ-< 3 _ _ $ begin-strict
      3 * nodes                     ≡⟨⟩
      nodes + 2 * nodes             <⟨ +-monoʳ-< nodes honest-majority ⟩
      nodes + 3 * length hs         ≤⟨ +-monoˡ-≤ _ xs≥n/3  ⟩
      3 * length xs + 3 * length hs ≡˘⟨ *-distribˡ-+ 3 (length xs) _ ⟩
      3 * (length xs + length hs)   ∎

    len∩ : length xs∩ > 0
    len∩ = begin-strict
      0                               ≡˘⟨ n∸n≡0 nodes ⟩
      nodes ∸ nodes                   <⟨ ∸-monoˡ-< len+ ≤-refl ⟩
      (length xs + length hs) ∸ nodes ≤⟨ length-∩ uxs uhs ⟩
      length xs∩                      ∎

    QED : Any Honest xs
    QED =
      let
        x , x∈ = nonEmpty∈ len∩
        x∈xs , x∈hs = ∈-∩⁻ x xs hs x∈
        _ , hx = L.Mem.∈-filter⁻ honest? {xs = allPids} x∈hs
      in
        L.Any.map (λ where refl → hx) x∈xs

  honestFromIncludesHonest : ∀ {pids} →
    ∙ Unique pids
    ∙ IncludesHonest pids
      ───────────────────
      Any Honest pids
  honestFromIncludesHonest uxs xs>n/3 = honestFromThird uxs (Nat.<⇒≤ xs>n/3)

  honestFromMajority : ∀ {pids} →
    ∙ Unique pids
    ∙ IsMajority pids
      ───────────────
      Any Honest pids
  honestFromMajority uxs maj = honestFromThird uxs (≤-trans (m≤m+n _ _) maj)

  majority-mono : ∀ {A : Type} {xs ys : List A} →
    ∙ Unique xs
    ∙ xs ⊆ˢ ys
    ∙ IsMajority xs
      ─────────────
      IsMajority ys
  majority-mono {xs = xs}{ys} ux xs⊆ˢys maj =
    begin 2 * nodes     ≤⟨  maj ⟩
          3 * length xs ≤⟨ Nat.*-monoʳ-≤ 3 $ ⊆ˢ-length ux xs⊆ˢys ⟩
          3 * length ys ∎

  moreThanF-mono : ∀ {A : Type} {xs ys : List A} →
    ∙ Unique xs
    ∙ xs ⊆ˢ ys
    ∙ MoreThanF xs
      ─────────────
      MoreThanF ys
  moreThanF-mono {xs = xs}{ys} ux xs⊆ˢys maj =
    begin 1 + nodes     ≤⟨ maj  ⟩
          3 * length xs ≤⟨ Nat.*-monoʳ-≤ 3 $ ⊆ˢ-length ux xs⊆ˢys ⟩
          3 * length ys ∎

  majority≡ = subst IsMajorityRatio

  majority⇒honest-majority : ∀ {xs : List Pid} →
    ∙ Unique xs
    ∙ IsMajority xs
      ──────────────────────────────────────────
      length xs < 2 * length (filter honest? xs)
  majority⇒honest-majority {xs = xs} u maj = begin-strict
      vs
    ≡⟨ vs≡ ⟩
      hs + ds
    <⟨ +-monoʳ-< hs ds<hs ⟩
     hs + hs
    ≡⟨ cong (hs +_) (sym $ +-identityʳ hs) ⟩
     2 * hs
    ∎
    where

    vs = length xs
    HS = filter honest? xs
    DS = filter dishonest? xs
    hs = length HS
    ds = length DS
    AD = filter dishonest? allPids --all dishonest pids
    ad = length AD

    uds : Unique DS
    uds = L.Unique.filter⁺ dishonest? u

    vs≡ : vs ≡ hs + ds

    vs≡ = filter-length honest? {xs = xs}

    ds<ad : ds ≤ ad
    ds<ad = ⊆ˢ-length {xs = DS} {ys = AD}
                      uds
                      (L.SubS.filter⁺′ dishonest? dishonest? (λ z → z) (allPids-complete xs))

    3ds<n : (3 * ds) < nodes
    3ds<n = begin-strict
        3 * ds
      ≤⟨ *-monoʳ-≤ 3 ds<ad ⟩
        3 * ad
      <⟨ dishonestMinority ⟩
        nodes
      ∎

    ds<hs : ds < hs
    ds<hs = *-cancelˡ-< 3 ds hs $
     begin-strict
       3 * ds
     ≡⟨ (sym $ m+n∸n≡m (3 * ds) (3 * ds)) ⟩
       (3 * ds) + (3 * ds) ∸ 3 * ds
       ≡⟨ cong ((_∸ 3 * ds) ∘ (3 * ds +_)) $ sym $ +-identityʳ (3 * ds)  ⟩
       2 * (3 * ds) ∸ 3 * ds
     <⟨ ∸-monoˡ-< {2 * (3 * ds)} {3 * ds} {2 * nodes} (*-monoʳ-< 2 3ds<n) (m≤n*m (3 * ds) 2) ⟩
       2 * nodes ∸ 3 * ds
     ≤⟨ +-cancelʳ-≤ (3 * ds) _ _ (
        begin
          2 * nodes ∸ 3 * ds + 3 * ds
        ≡⟨ m∸n+n≡m (≤-trans (<⇒≤ 3ds<n) (m≤m+n nodes _)) ⟩
          2 * nodes
        ≤⟨ maj ⟩
         3 * vs
        ≡⟨ cong (3 *_) vs≡ ⟩
         3 * (hs + ds)
        ≡⟨ *-distribˡ-+ 3 hs ds ⟩
          3 * hs + 3 * ds
        ∎
       ) ⟩
       3 * hs
     ∎

  module _ {A B : Type} xs (f : A → B) (let len≡ = L.length-map f xs) where
    majority-map⁺ = majority≡ (sym len≡)
    majority-map⁻ = majority≡ len≡

  private variable A : Type; xs : List A

  Majority⇒∃ : IsMajority xs → ∃ (_∈ xs)
  Majority⇒∃ {xs = []}    p = ⊥-elim $ majority⁺ p
  Majority⇒∃ {xs = _ ∷ _} _ = -, here refl

  MoreThanF⇒∃ : MoreThanF xs → ∃ (_∈ xs)
  MoreThanF⇒∃ {xs = []}    p = ⊥-elim $ moreThanF⁺ p
  MoreThanF⇒∃ {xs = _ ∷ _} _ = -, here refl

  open import Prelude.PVec Honest ⦃ Dec-Honest ⦄ public
    hiding  (_[_]%=′_)
    renaming ( PVec to HonestVec; pFins to honestPids; PIndex to HonestPid
             ; pLookup to pLookup′; _[_]≔_ to _[_]≔′_; _[_]%=_ to _[_]%=′_
             )

  pLookup : HonestVec A → (p : Pid) ⦃ _ : Honest p ⦄ → A
  pLookup xs p = pLookup′ xs (p ,· it)

  infixl 6 _[_]%=_ _[_]≔_

  _[_]≔_ : HonestVec A → (p : Pid) ⦃ _ : Honest p ⦄ → A → HonestVec A
  xs [ p ]≔ y = xs [ p ,· it ]≔′ y

  _[_]%=_ : HonestVec A → (p : Pid) ⦃ _ : Honest p ⦄ → (A → A) → HonestVec A
  xs [ p ]%= f = xs [ p ,· it ]%=′ f
```
