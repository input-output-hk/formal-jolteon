{-# OPTIONS --safe #-}
open import Prelude
open import Hash
open import Jolteon.Assumptions

module Jolteon.Properties.Votes.NotGenesis (⋯ : _) (open Assumptions ⋯) where

open import Jolteon ⋯
open import Jolteon.Properties.Core ⋯
open import Jolteon.Properties.Votes.Core ⋯

honest∈votes⇒¬Genesis : ∀ {s} → Reachable s → let ms = s .history in
  ∙ Honest p
  ∙ p ∈ votes b ms
    ───────────────
    ¬Genesis b
honest∈votes⇒¬Genesis (_ , refl , (_ ∎)) _ ()
honest∈votes⇒¬Genesis {p = p} {b = b} (_ , s-init , (_ ⟨ st ∣ s ⟩←— tr)) hp p∈
  with IH ← honest∈votes⇒¬Genesis {p = p} {b = b} (_ , s-init , tr) hp
  with st
... | WaitUntil _ _ _
  = IH p∈
... | Deliver _
  = IH p∈
... | DishonestLocalStep {env = env} {p = p′} ¬hp′ ¬frg
  = QED
  where
  QED : ¬Genesis b
  QED
    -- p∈ : p ∈ votes b (env .content ∷ s .history)
    with env .content
  ... | Propose  _ = IH p∈
  ... | TCFormed _ = IH p∈
  ... | Timeout _  = IH p∈
  ... | Vote vs
    -- p∈ : p ∈ votes b (Vote vs ∷ s .history)
    with vs ∙blockId ≟ b ∙blockId
    -- p∈ : p ∈ votes b (s .history)
  ... | no  _ = IH p∈
    -- p∈ : p ∈ nub (vs ∙pid ∷ votes' b (s .history))
  ... | yes vs≡
    with vs ∙pid ∈? votes' b (s .history)
    -- p∈ : p ∈ votes b (s .history)
  ... | yes _ = IH p∈
    -- p∈ : p ∈ vs ∙pid ∷ votes b (s .history)
  ... | no _
    with ⟫ p∈
  ... | ⟫ there p∈ = IH p∈
  ... | ⟫ here refl
    = noHashCollision˘
... | LocalStep {p = p′} {menv = menv} {ls′ = ls′} st
  with st
... | InitTC _ _ = IH p∈
... | InitNoTC _ _ = IH p∈
... | ProposeBlockNoOp _ _ = IH p∈
... | RegisterProposal _ _ _ _ _ = IH p∈
... | EnoughTimeouts _ _ _ _ = IH p∈
... | RegisterTimeout _ _ _ _ = IH p∈
... | RegisterTC _ _ _ _ = IH p∈
... | TimerExpired _ _ = IH p∈
... | RegisterVote _ _ _ _ _ _ = IH p∈
... | AdvanceRoundQC _ _ _ = IH p∈
... | AdvanceRoundTC _ _ _ = IH p∈
... | AdvanceRoundNoOp _ _ _ = IH p∈
... | Lock _ _ = IH p∈
... | CommitNoOp _ _ = IH p∈
... | VoteBlockNoOp _ _ = IH p∈
... | Commit _ _ = IH p∈
... | ProposeBlock _ _ = IH p∈
... | VoteBlock {b = b′} _ _ _
  with b′ ∙blockId ≟ b ∙blockId
... | no _
  = IH p∈
... | yes b♯≡
  with p′ ∈? votes' b (s .history)
... | yes _
  = IH p∈
... | no _
  with p∈
... | there ≪p∈ = IH ≪p∈
... | here p≡ = noHashCollision˘
