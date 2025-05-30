{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Local.Slice (⋯ : _) (open Assumptions ⋯) (p : Pid)⦃ hp : Honest p ⦄ where

open import Jolteon.Block ⋯ hiding (p)
open import Jolteon.Message ⋯
open import Jolteon.Local.State ⋯
open import Jolteon.Local.Step ⋯
open import Jolteon.Global.State ⋯

record SliceState : Type where
  constructor mkSliceState
  field currentTime : Time
        pls         : LocalState
        history     : Messages

open SliceState public

variable ss ss′ : SliceState

updateSs : LocalState → Maybe Envelope → SliceState → SliceState
updateSs ls me ss =
  let ms = L.fromMaybe (M.map _∙message me)
  in record ss { pls = ls ; history = ms ++ ss .history }

sliceReceiveMessage : Message → Op₁ SliceState
sliceReceiveMessage m ss =
  let ls  = ss .pls
      ls′ = record ls { inbox = ls .inbox L.∷ʳ m }
  in record ss { pls = ls′ }

data _—→ᴸ_  (ss : SliceState) : SliceState → Type where
  LocalStep :
    p ⦂ ss .currentTime ⊢ ss .pls — menv —→ ls′
    ───────────────────────────────────────────
    ss —→ᴸ updateSs ls′ menv ss

  Deliver : ∀ m →
    ───────────────────────────────
    ss —→ᴸ sliceReceiveMessage m ss

  WaitUntil : ∀ t →
    ss .currentTime < t
    ───────────────────────────────────
    ss —→ᴸ record ss { currentTime = t }

open import Prelude.Closures _—→ᴸ_ public
  using ()
  renaming
    ( begin_ to beginᴸ_; _∎ to _∎ᴸ
    ; _—↠_ to _—↠ᴸ_; _—→⟨_⟩_ to _—→ᴸ⟨_⟩_
    ; _←—_ to _←—ᴸ_; _↞—_ to _↞—ᴸ_; _⟨_⟩←—_ to _⟨_⟩←—ᴸ_; _⟨_∣_⟩←—_ to _⟨_∣_⟩←—ᴸ_
    )
