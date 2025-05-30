{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Steps.Now (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Steps.Core ⋯
open import Jolteon.Properties.State ⋯

initsTCNow : ∀ {tc : TC} {s} ⦃ _ : Honest p ⦄ (Rs : Reachable s) →
  let ls = s ＠ p; t = s .currentTime in
  ∀ {st : p ⦂ s .currentTime ⊢ ls — menv —→ ls′} →
  let s′ = broadcast t menv (s ＠ p ≔ ls′) in
  StepInitsTC tc (_ ⊢ st)
  ───────────────────────────────
    (ls .tc-last ≡ just tc)
  × (ls .r-cur   ≡ 1 + tc ∙round)
initsTCNow {p = p} {tc = tc} {s = s} Rs {st} st-initTC
  with st | st-initTC
... | InitTC {tc = .tc} ph≡ tc≡ | refl
  = tc≡ , r≡
  where
  _ls = s ＠ p

  r≡ : _ls .r-cur ≡ 1 + tc ∙round
  r≡ = M.All.drop-just $ subst (All _) tc≡ (tc-last-r≡ Rs)

proposesNow : ∀ {b : Block} {s}  ⦃ _ : Honest p ⦄ (Rs : Reachable s) →
  let ls = s ＠ p; t = s .currentTime in
  ∀ {st : p ⦂ s .currentTime ⊢ ls — menv —→ ls′} →
  let s′ = broadcast t menv (s ＠ p ≔ ls′) in
  ∙ b ∙∉ s  .history
  ∙ b ∙∈ s′ .history
    ───────────────────────
    StepProposes b (_ ⊢ st)
proposesNow {p = p} {s = s} Rs {st} b∉ b∈
  with st
... | InitTC _ _ = b∉ b∈
... | InitNoTC _ _ = b∉ b∈
... | ProposeBlockNoOp _ _ = b∉ b∈
... | RegisterProposal _ _ _ _ _ = b∉ b∈
... | EnoughTimeouts _ _ _ _ = b∉ b∈
... | RegisterTimeout _ _ _ _ = b∉ b∈
... | RegisterTC _ _ _ _ = b∉ b∈
... | TimerExpired _ _ = b∉ b∈
... | RegisterVote _ _ _ _ _ _ = b∉ b∈
... | AdvanceRoundQC _ _ _ = b∉ b∈
... | AdvanceRoundTC _ _ _ = b∉ b∈
... | AdvanceRoundNoOp _ _ _ = b∉ b∈
... | Lock _ _ = b∉ b∈
... | CommitNoOp _ _ = b∉ b∈
... | VoteBlock _ _ _ = b∉ b∈
... | VoteBlockNoOp _ _ = b∉ b∈
... | Commit _ _ = b∉ b∈
... | ProposeBlock {txn = txn} _ _
  with b∈
... | there b∈ = ⊥-elim $ b∉ b∈
... | here b≡  = b≡
