{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Votes.Core (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯

-- ** Counting honest votes (≥ f + 1)

-- NB: might contain duplicates (e.g. from adversary replaying honest messages)

getHonestVoteFor : Block → Message → Maybe Pid
getHonestVoteFor b m = case m of λ where
  (Vote vs)    → M.when (isHonest (vs ∙pid) ∧ (vs ∙blockId == b ∙blockId)) (vs ∙pid)
  (Propose _)  → nothing
  (TCFormed _) → nothing
  (Timeout _)  → nothing

honestVotes' : Block → Messages → List Pid
honestVotes' b ms = flip L.mapMaybe ms $ getHonestVoteFor b

honestVotes : Block → Messages → List Pid
honestVotes = nub ∘₂ honestVotes'

MoreThanF-Honest : Block → GlobalState → Type
MoreThanF-Honest b s = MoreThanF $ honestVotes b (s .history)

Honest-honestVotes' : ∀ b ms → All Honest (honestVotes' b ms)
Honest-honestVotes' b [] = []
Honest-honestVotes' b (Propose _ ∷ ms) = Honest-honestVotes' b ms
Honest-honestVotes' b (Vote vs ∷ ms) with honest? (vs ∙pid) | vs ∙blockId ≟ b ∙blockId
... | no _   | _     = Honest-honestVotes' b ms
... | yes hp | no _  = Honest-honestVotes' b ms
... | yes hp | yes _ = hp ∷ Honest-honestVotes' b ms

Honest-honestVotes' b (TCFormed _ ∷ ms) = Honest-honestVotes' b ms
Honest-honestVotes' b (Timeout _ ∷ ms) = Honest-honestVotes' b ms

Honest-honestVotes : ∀ b ms → All Honest (honestVotes b ms)
Honest-honestVotes b ms = All-nub⁺ (Honest-honestVotes' b ms)

honestVotes-mono : ∀ ms m →
  length (honestVotes b ms) ≤ length (honestVotes b (m ∷ ms))
honestVotes-mono {b} ms m with getHonestVoteFor b m
... | nothing = Nat.≤-refl
... | just p = nub-length {xs = honestVotes' b ms}{p}

{-
The following lemma (which uses sublists):
  honestVotes⊆ : ms ⊆ ms′ → honestVotes b ms ⊆ honestVotes b ms′

is *not true* because sublists are not preserved by nub.

  FALSE -> nub-SubList : xs ⊆ ys → nub xs ⊆ nub ys

  [ 3 , 5 ] ⊆ [ 3 , 5 , 3 ] , but
  nub [ 3 , 5 ] ≡ [ 3 , 5 ] ¬⊆ [ 5 , 3 ] ≡ nub  [ 3 , 5 , 3 ]
-}

-- ** Counting votes (≥ 2*f + 1)

getVoteFor : Block → Message → Maybe Pid
getVoteFor b m = case m of λ where
  (Vote vs)    → M.when (vs ∙blockId == b ∙blockId) (vs ∙pid)
  (Propose _)  → nothing
  (TCFormed _) → nothing
  (Timeout _)  → nothing

-- NB: might contain duplicates (e.g. from adversary replaying honest messages)
votes' : Block → Messages → List Pid
votes' b ms = L.mapMaybe (getVoteFor b) ms

honestVotes'≡ : ∀ b ms → honestVotes' b ms ≡ filter honest? (votes' b ms)
honestVotes'≡ b [] = refl
honestVotes'≡ b (Propose _ ∷ ms) = honestVotes'≡ b ms
honestVotes'≡ b (Vote vs ∷ ms) with honest? (vs ∙pid) | vs ∙blockId ≟ b ∙blockId
... | no _   | no _ = honestVotes'≡ b ms
... | no ¬p  | yes _ =
  trans (honestVotes'≡ b ms)
        (sym $ L.filter-reject honest? ¬p)
... | yes hp | no _  = honestVotes'≡ b ms
... | yes hp | yes _ =
  trans (cong ((vs ∙pid) ∷_) $ honestVotes'≡ b ms)
        (sym $ L.filter-accept honest? hp)
honestVotes'≡ b (TCFormed _ ∷ ms) = honestVotes'≡ b ms
honestVotes'≡ b (Timeout _ ∷ ms) = honestVotes'≡ b ms

votes : Block → Messages → List Pid
votes = nub ∘₂ votes'

honestVotes≡ : ∀ b ms → honestVotes b ms ≡ filter honest? (votes b ms)
honestVotes≡ b ms
  rewrite sym $ nub-filter {xs = votes' b ms} honest?
  rewrite honestVotes'≡ b ms = refl

p∈⇒hp : ∀ b ms →
  p ∈ honestVotes b ms
  ────────────────────
  p ∈ votes b ms × Honest p
p∈⇒hp b ms p∈ rewrite honestVotes≡ b ms = L.Mem.∈-filter⁻ honest? p∈

MajorityVotes : Block → GlobalState → Type
MajorityVotes b s = IsMajority $ votes b (s .history)

Majority⇒MoreThanF : ∀ (ps : List Pid) →
  ∙ Unique ps
  ∙ IsMajority ps
    ─────────────────────────────
    MoreThanF (filter honest? ps)
Majority⇒MoreThanF ps u maj =
  *-cancelˡ-< 2 nodes (3 * hvs) $
  begin-strict
    2 * nodes
  ≤⟨ maj ⟩
    3 * _vs
  <⟨ *-monoʳ-< 3 vs<2*hvs ⟩
    3 * (2 * hvs)
  ≡⟨ (sym $ *-assoc 3 2 hvs) ⟩
    6 * hvs
  ≡⟨ *-assoc 2 3 hvs ⟩
    2 * (3 * hvs)
  ■
  where
    open Nat ; open ≤-Reasoning renaming (_∎ to _■)

    _vs = length $ ps
    hvs = length $ filter honest? ps

    vs<2*hvs : _vs < 2 * hvs
    vs<2*hvs = majority⇒honest-majority u maj

{- was Majority⇒MoreThanF
MajorityVotes⇒MoreThanF-Honest : ∀ {s} → Reachable s →
  MajorityVotes b s
  ────────────────────
  MoreThanF-Honest b s
MajorityVotes⇒MoreThanF-Honest {b} {s} Rs maj
  rewrite honestVotes≡ b (s .history)
  = let ps  = votes b (s .history)
        ps′ = votes' b (s .history)
    in Majority⇒MoreThanF ps (Unique-nub {xs = ps′}) maj
-}
