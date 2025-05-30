
# Global state of the entire system.

<!--
```agda
{-# OPTIONS --safe #-}
open import Prelude
open import Hash

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.State (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
open import Jolteon.Message ⋯
open import Jolteon.Local.State ⋯
```
-->

The global state consists of a local state for each individual node.
```agda
StateMap : Type
StateMap = HonestVec LocalState
```

Other than that, it recors in-flight messages, and
the whole history of previous messages.
```agda
TPMessage  = Time × Pid × Message
TPMessages = List TPMessage

record GlobalState : Type where
  constructor mkGlobalState
  field
    currentTime   : Time
    stateMap      : StateMap  -- A map assigning each PID its local state.
    networkBuffer : TPMessages -- Messages in transit on the network.
    history       : Messages  -- All messages seen so far.
```
<!--
```agda
open GlobalState public
variable s s′ s″ : GlobalState
```
-->

The initial global state starts at epoch 1 with no messages and initial local states.
```agda
initStateMap : StateMap
initStateMap = V.replicate _ initLocalState

initGlobalState : GlobalState
initGlobalState = mkGlobalState 0 initStateMap [] []
```
<!--
```agda
instance Def-StateMap     = Default _ ∋ λ where .def → initStateMap
         Def-GlobalState  = Default _ ∋ λ where .def → initGlobalState
         Init-GlobalState = HasInitial _ ∋ λ where .Initial → _≡ initGlobalState
```
-->
```agda
-- Retrieve a replica's local state.
_＠ᵐ_ : StateMap → ∀ p ⦃ _ : Honest p ⦄ → LocalState
sm ＠ᵐ p = pLookup sm p

_＠ᵐᵖ_ : StateMap → HonestPid → LocalState
sm ＠ᵐᵖ hp = pLookup′ sm hp

_＠_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → LocalState
s ＠ p = s .stateMap ＠ᵐ p

_＠ʰ_ : GlobalState → ∀ {p} → Honest p → LocalState
s ＠ʰ hp = pLookup′ (s .stateMap) (_ ,· hp)

_＠ʰᵖ_ : GlobalState → HonestPid → LocalState
s ＠ʰᵖ hp = pLookup′ (s .stateMap) hp

-- Update a replica's local state.
_＠_%=_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → Op₁ LocalState → GlobalState
s ＠ p %= f = record s
  { stateMap = s .stateMap [ p ]%= f }

-- Set a replica's local state.
_＠_≔_ : GlobalState → ∀ p ⦃ _ : Honest p ⦄ → LocalState → GlobalState
s ＠ p ≔ ls = record s
  { stateMap = s .stateMap [ p ]≔ ls }
```
-->
