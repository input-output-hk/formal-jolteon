<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Assumptions

module Jolteon.Decidability.HighestQC (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Decidability.Core ⋯
open import Jolteon.Decidability.VoteSharesOf ⋯

open L.All using (tabulate; map⁻; map⁺; lookup)
```
-->

### The `allQCs` function and its properties

The function allQCs extracts allQCs in a list of messages.

```agda
-- Decide if it is possible to construct a FormedQC in ms with the data d.
Dec-∃FormedQC : ∀ d ms → Dec (∃ λ qc → (qc .payload ≡ d) × FormedQC qc ms)
Dec-∃FormedQC d ms
  with ¿ UniqueMajority⊆ˢ $ map node (voteShares d ms) ¿
... | no ¬ums
  = no λ where
  (qc , refl , all∈) →
    ¬ums $ qc .shares
         , voteShares-maximal qc ms all∈
         , getUnique qc
         , getQuorum qc
... | yes (ps , ps⊆ , uniq , maj)
  = yes (myqc , refl , vss∈)
  where
  myqc : QC
  myqc = record
    { payload      = d
    ; shares       = ps
    ; uniqueShares = uniq
    ; quorum       = maj }

  all∈ : All (_∈ map node (voteShares d ms)) ps
  all∈ = tabulate ps⊆

  voteShares⊆ˢms : map Vote (voteShares d ms) ⊆ˢ ms
  voteShares⊆ˢms = lookup {P = _∈ _} $ map⁺ (voteShares-sound d ms)

  _vss = map (d signed-by_) ps

  shares⊆ˢvoteShares : map Vote _vss ⊆ˢ map Vote (voteShares d ms)
  shares⊆ˢvoteShares
    = L.SubS.map⁺ Vote
    $ subst (map (d signed-by_) ps ⊆ˢ_)
            (sym $ voteShares-lemma d ms)
            (L.SubS.map⁺ (d signed-by_) ps⊆)

  vss⊆ˢ : map Vote _vss ⊆ˢ ms
  vss⊆ˢ = L.SubS.⊆-trans shares⊆ˢvoteShares voteShares⊆ˢms

  vss∈ : All (_∙∈ ms) _vss
  vss∈ = map⁻ (tabulate vss⊆ˢ)

-- Decide if it is possible to construct a FormedQC with the given VoteShare and
-- list of messages, where the VoteShare is considered as an additional Vote.
tryQC : ∀ vs ms →
  ─────────────────────────────────────────────────────────────────────
  Dec $ ∃ λ qc → (qc .payload ≡ vs .datum) × FormedQC qc (Vote vs ∷ ms)
tryQC vs ms = Dec-∃FormedQC (vs .datum) (Vote vs ∷ ms)

record AllQCsOf (ms : Messages) (qcs : QCs) : Type where
  field
    genesis∈ : qc₀ ∈ qcs
    sound    : qc ∈ qcs → qc ∙∈ ms
    complete : qc ∙∈ ms → qc .payload ∈ map payload qcs

open AllQCsOf
open L.All using () renaming (map to amap; zipWith to azipWith)
open L.Any using (tail; ++⁺ˡ)
open L.Mem using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)

allQCs⁺ : (ms : Messages) → ∃ (AllQCsOf ms)
allQCs⁺ []
  = let qc₀∈ = here refl in
  [ qc₀ ] , record
  { genesis∈ = qc₀∈
  ; sound    = λ where (here refl) → initialQC refl
  ; complete = λ where (initialQC refl) → ∈-map⁺ payload {x = qc₀} qc₀∈
                       {qc} (formedQC p) → ⊥-elim $ ¬FormedQC-[] qc p
  }
allQCs⁺ (m ∷ ms)
  with qs , r ← allQCs⁺ ms
  with m
... | Propose (b signed-by p)
  = _qcs , record
  { genesis∈ = qc₀∈
  ; sound    = isSound
  ; complete = λ where
    (initialQC refl) → ∈-map⁺ payload qc₀∈
    {qc} (formedQC p) → there $′
      case ¿ qc ∈ tcqs ¿ of λ
      where
      (yes qc∈tc) → ∈-map⁺ payload (++⁺ˡ qc∈tc)
      (no _) → subst (_ ∈_) (sym $ L.map-++ payload _ qs) $
                 ∈-++⁺ʳ _ $ r .complete $ formedQC {qc} $ amap (tail λ ()) p
    (receivedQC (here (qc∈-Propose refl))) → here refl
    (receivedQC (here (qc∈-ProposeTC refl qc∈))) →
      there $′ ∈-map⁺ payload (++⁺ˡ qc∈)
    (receivedQC (there p)) → there $′
      subst (_ ∈_) (sym (L.map-++ payload _ qs)) $
      ∈-++⁺ʳ _ $ r .complete (receivedQC p)
  }
  where
  tcqs = M.fromMaybe [] (M.map qcs (b ∙tc?))
  _qcs = b .blockQC ∷ tcqs ++ qs

  tcqs≡[] : b ∙tc? ≡ nothing → tcqs ≡ []
  tcqs≡[] refl = refl

  tcqs≡ : b ∙tc? ≡ just tc → tcqs ≡ qcs tc
  tcqs≡ refl = refl

  qc₀∈ : qc₀ ∈ _qcs
  qc₀∈ = there $′ ∈-++⁺ʳ tcqs $ r .genesis∈

  isSound : qc ∈ _qcs → qc ∙∈ (Propose (b signed-by p) ∷ ms)
  isSound (here eq)   = receivedQC $ here $′ qc∈-Propose eq
  isSound {qc} (there qc∈)
    with ∈-++⁻ tcqs qc∈
  ... | inj₂ qc∈ʳ = qc∈-monotonic (r .sound qc∈ʳ)
  ... | inj₁ qc∈ˡ
    = receivedQC (here QED)
    where
    QED : qc qc∈-Message Propose (b signed-by p)
    QED with b ∙tc? in tc≡
    ... | nothing
      = contradict qc∈ˡ
    ... | just tc
      = qc∈-ProposeTC tc≡ qc∈ˡ

... | TCFormed tc
  = let qc₀∈ = ∈-++⁺ʳ (qcs tc) (r .genesis∈) in
  qcs tc ++ qs , record
  { genesis∈ = qc₀∈
  ; sound    = λ qc∈ → case ∈-++⁻ (qcs tc) qc∈ of λ
    where (inj₁ qc∈) → receivedQC $ here $′ qc∈-TCFormed qc∈
          (inj₂ qc∈) → qc∈-monotonic (r .sound qc∈)
  ; complete = λ where
    (initialQC refl) → ∈-map⁺ payload qc₀∈
    {qc} (formedQC p) → case ¿ qc ∈₁ (qcs⁺ tc) ¿ of λ
      where
      (yes qc∈tc) → ∈-map⁺ payload (++⁺ˡ qc∈tc)
      (no _) → there $′
        subst (_ ∈_) (sym $ L.map-++ payload _ qs) $
        ∈-++⁺ʳ _ $ r .complete $ formedQC {qc} $ amap (tail λ ()) p
    (receivedQC (here (qc∈-TCFormed p))) → ∈-map⁺ payload (∈-++⁺ˡ p)
    (receivedQC (there p)) → there $′
      subst (_ ∈_) (sym (L.map-++ payload _ qs)) $
      ∈-++⁺ʳ _ $ r .complete (receivedQC p)
  }
... | Timeout (te , mtc)
  = _qcs , record {
    genesis∈ = qc₀∈
  ; sound    = isSound
  ; complete = λ where
    (initialQC refl) → ∈-map⁺ payload qc₀∈
    {qc} (formedQC p) → there $′
      case ¿ qc ∈ tcqs ¿ of λ
      where
      (yes qc∈tc) → ∈-map⁺ payload (++⁺ˡ qc∈tc)
      (no _) → subst (_ ∈_) (sym $ L.map-++ payload _ qs) $
                 ∈-++⁺ʳ _ $ r .complete $ formedQC {qc} (amap (tail λ ()) p)
    (receivedQC p) → case p of λ
      where
      (here (qc∈-Timeout refl)) → here refl
      (here (qc∈-TimeoutTC refl qc∈)) →
        there $′ ∈-map⁺ payload (++⁺ˡ qc∈)
      (there p) → there $′
        subst (_ ∈_) (sym (L.map-++ payload _ qs)) $
        ∈-++⁺ʳ _ $ r .complete (receivedQC p)
  }
  where
  tcqs = M.fromMaybe [] (M.map qcs mtc)
  _qcs = te ∙qcTE ∷ tcqs ++ qs

  tcqs≡[] : mtc ≡ nothing → tcqs ≡ []
  tcqs≡[] refl = refl

  tcqs≡ : mtc ≡ just tc → tcqs ≡ qcs tc
  tcqs≡ refl = refl

  qc₀∈ : qc₀ ∈ _qcs
  qc₀∈ = there $′ ∈-++⁺ʳ tcqs $ r .genesis∈

  isSound : qc ∈ _qcs → qc ∙∈ (Timeout (te , mtc) ∷ ms)
  isSound  (here eq) = receivedQC $ here $′ qc∈-Timeout eq
  isSound {qc} (there qc∈)
    with ∈-++⁻ tcqs qc∈
  ... | inj₂ qc∈ʳ = qc∈-monotonic (r .sound qc∈ʳ)
  ... | inj₁ qc∈ˡ = receivedQC (here QED)
    where
    QED : qc qc∈-Message Timeout (te , mtc)
    QED
      with ⟫ mtc
    ... | ⟫ nothing = contradict qc∈ˡ
    ... | ⟫ just tc = qc∈-TimeoutTC refl qc∈ˡ
... | Vote v
  with tryQC v ms
... | no ¬qc
  = let qc₀∈ = r .genesis∈ in
  qs , record
  { genesis∈ = qc₀∈
  ; sound    = qc∈-monotonic ∘ r .sound
  ; complete = λ where
    (initialQC refl) → ∈-map⁺ payload qc₀∈
    {qc} (formedQC p) → case qc .payload ≟ v .datum of λ
      where
      (yes eq) → ⊥-elim $ ¬qc (qc , eq , p)
      (no ¬eq) → r .complete $ formedQC {qc} $
        azipWith (λ where (v∈ , refl) → tail (λ where refl → ¬eq refl) v∈)
                 (p , qcVoteShares-All qc)
    (receivedQC (there p)) → r .complete (receivedQC p)
  }
... | yes (qc , refl , vs)
  = let qc₀∈ = there $ r .genesis∈ in
  qc ∷ qs , record
  { genesis∈ = qc₀∈
  ; sound    = λ where
    (here refl) → formedQC vs
    (there qc∈) → qc∈-monotonic $ r .sound qc∈
  ; complete = λ where
    (initialQC refl) → ∈-map⁺ payload qc₀∈
    {qc} (formedQC p) → case qc .payload ≟ v .datum of λ
      where
      (yes eq) → here eq
      (no ¬eq) → there $ r .complete $ formedQC {qc} $
        azipWith (λ where (v∈ , refl) → tail (λ where refl → ¬eq refl) v∈)
                          (p , qcVoteShares-All qc)
    (receivedQC (there p)) → there $ r .complete (receivedQC p)
  }

module _ (ms : Messages) (let qs , r = allQCs⁺ ms) where
  allQCs : QCs
  allQCs = qs

  open AllQCsOf r public renaming
    ( sound    to allQCs-sound
    ; complete to allQCs-complete
    )

instance
  Dec-AllQC : ∀ {r} → AllQC (λ qc → qc ∙round < r) ⁇¹
  Dec-AllQC {r = r} {x = ms} .dec = mapDec All⇒AllQC AllQC⇒All dec
    where
    P = λ qc → qc ∙round < r

    All⇒AllQC : All P (allQCs ms) → AllQC P ms
    All⇒AllQC allP = mk (lookup (L.All.map⁺ allP) ∘′ allQCs-complete ms)

    AllQC⇒All : AllQC P ms → All P (allQCs ms)
    AllQC⇒All (mk allP) = L.All.tabulate (allP ∘ allQCs-sound _)

highestQC∈ : (ms : Messages) → QC
highestQC∈ ms = case allQCs ms of λ where
  []       → qc₀
  (q ∷ qs) → maxNE (q ∷ qs)

highestQC∈-is∈ : ∀ ms →
  ───────────────────
  highestQC∈ ms ∙∈ ms
highestQC∈-is∈ ms with allQCs ms in eq
... | []     = initialQC refl
... | q ∷ qs = allQCs-sound ms (subst (_ ∈_) (sym eq) (highestQC∈List q qs))

highestQC∈-isHighest : ∀ ms qc′ →
  qc′ ∙∈ ms
  ───────────────────────
  qc′ ≤qc (highestQC∈ ms)
highestQC∈-isHighest ms qc′ qc′∈
  with allQCs-complete ms qc′∈ | allQCs ms in eq
... | qcp∈ | q ∷ qs
  = maxNE-correct {qc′}{q ∷ qs}
  $ subst (_ ∈_) (cong (map _) eq) qcp∈
... | qcp∈ | []
  = case subst (λ ◆ → _ ∈ map _ ◆) eq qcp∈ of λ ()

highestQC∈-mono : ∀ m ms →
  ─────────────────────────────────────
  highestQC∈ ms ≤qc highestQC∈ (m ∷ ms)
highestQC∈-mono m ms
  = highestQC∈-isHighest (m ∷ ms) (highestQC∈ ms)
  $ qc∈-monotonic (highestQC∈-is∈ ms)
```

### Decidability of highest-qc-∈

```agda
instance
  Dec-highest-qc-∈ : _-highest-qc-∈-_ ⁇²
  Dec-highest-qc-∈ {qc} {ms} .dec with dec
  ... | no ¬qc∈ = no λ where (isHighest qch∈ _) → ¬qc∈ qch∈
  ... | yes qc∈ with qc <qc? highestQC∈ ms
  ... | yes qc< = no λ where
    (isHighest _ qch) → Nat.<⇒≱ qc< (qch (highestQC∈ ms) (highestQC∈-is∈ ms))
  ... | no ¬qc< = yes $
    isHighest qc∈ λ qc′ qc′∈ →
      Nat.≤-trans (highestQC∈-isHighest ms qc′ qc′∈) (Nat.≮⇒≥ ¬qc<)
```
