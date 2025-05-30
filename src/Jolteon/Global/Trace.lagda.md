
# Traces of multiple global steps

<!--
```agda
{-# OPTIONS --safe #-}
{-# OPTIONS --with-K #-}
open import Prelude

open import Jolteon.Base
open import Jolteon.Assumptions

module Jolteon.Global.Trace (⋯ : _) (open Assumptions ⋯) where

open import Jolteon.Block ⋯
open import Jolteon.Message ⋯
open import Jolteon.Local.State ⋯
open import Jolteon.Local.Step ⋯
open import Jolteon.Global.State ⋯
open import Jolteon.Global.Step ⋯
```
-->

## Traces

We consider **traces** of the (global) step relation,
defined as its *reflexive-transitive closure*, and use these to prove invariants
as state predicates:

```agda
open import Prelude.Closures _—→_ public
  using ( begin_; _∎ ; _↞—_; _⟨_⟩←—_; _⟨_∣_⟩←—_; ↞—-trans
        ; _—↠_; —↠-trans; _—→⟨_⟩_; _—→⟨_∣_⟩_; _`—→⟨_⟩_; factor; factor⁺; Reachable-inj
        ; Reachable; Invariant; StepPreserved; Step⇒Invariant
        ; Trace; TraceProperty; TraceInvariant
        ; viewLeft; viewRight; viewLeft∘viewRight
        ; states⁺; states; states⁺-↞—; states-↞—; states⁺∘viewLeft
        )
  renaming (_←—_ to _¹←—_)

StateProperty = GlobalState → Type
```

Now, we can consider a specific local step occurring within a sequence of global transitions:

```agda
record Step : Type where
  constructor _⊢_
  field
    stepArgs : _ × _ × _ × _ × _
    theStep  : let p , t , ls , menv , ls′ = stepArgs in
               p ⦂ t ⊢ ls — menv —→ ls′
    ⦃ hp ⦄ : Honest (stepArgs .proj₁)
open Step public
  hiding (hp)

-- doStep : Step → Op₁ GlobalState
-- doStep st s = let p , _ , _ , menv , ls′ = st .stepArgs in
--   broadcast menv (s ＠ p ≔ ls′)

LocalStepProperty = Step → Type

allLocalSteps : (s′ ↞— s) → List Step
allLocalSteps = λ where
  (_ ∎) → []
  (_ ⟨ LocalStep st ⟩←— tr) → (_ ⊢ st) ∷ allLocalSteps tr
  (_ ⟨ _ ⟩←— tr) → allLocalSteps tr

_∋⋯_ : Reachable s → LocalStepProperty → Type
(_ , _ , tr) ∋⋯ P = Any P (allLocalSteps tr)

record Segment (A B : Type) : Type where
  constructor from_to_
  field _∙start _∙end : B → A
open Segment ⦃...⦄ public

instance
  Segment-↞ : Segment GlobalState (s′ ↞— s)
  Segment-↞ {s′}{s} = from (const s) to (const s′)

  Segment-→ : Segment LocalState (p ⦂ t ⊢ ls — menv —→ ls′)
  Segment-→ {ls = ls} {ls′ = ls′} = from (const ls) to (const ls′)

  Segment-Step : Segment LocalState Step
  Segment-Step = from (_∙start ∘ theStep) to (_∙end ∘ theStep)
```

```
extendRs : (Rs : Reachable s) → s′ ↞— s → Reachable s′
extendRs (_ , init , tr) tr′ = _ , init , ↞—-trans tr′ tr

_▷_ : GlobalState → LocalStepProperty → Type
s ▷ P = ∃ λ st →
          let p , t , ls , _ , _ = stepArgs st in
            t ≡ s .currentTime
          × s ＠ p ≡ ls
          × P st

▷-doStep : ∀ {P} → s ▷ P → GlobalState
▷-doStep {s = s} (st , _) = let p , t , _ , menv , ls′ = st .stepArgs in
  broadcast t menv (s ＠ p ≔ ls′)

_◃_ : LocalStepProperty → GlobalState → Type
P ◃ s′ = ∃ λ st → ∃ λ s →
          let p , t , ls , menv , ls′ = stepArgs st in
            t ≡ s .currentTime
          × s ＠ p ≡ ls
          × s′ ≡ broadcast t menv (s ＠ p ≔ ls′)
          × P st

record TraceExtension (Rs : Reachable s) : Type where
  constructor ⟨_,_,_,_⟩
  field
    intState   : GlobalState
    reachable′ : Reachable intState
    extension  : s ↞— intState
    traceAgree : Rs ≡ extendRs reachable′ extension
open TraceExtension

traceRs◃ :  ∀ (Rs : Reachable s){P} →
  (trP : Rs ∋⋯ P) →
  ────────────────────────────────────────────────
  Σ (TraceExtension Rs) (λ trE → P ◃ intState trE)
traceRs◃ (_ , init , (s ⟨ Deliver tpm∈ ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◃ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ Deliver tpm∈ ⟩←— tr⟪) , refl ⟩ , p
traceRs◃ Rs@(_ , init , tr@(s′ ⟨ LocalStep st ∣ s ⟩←— _)) (here px)
 =   ⟨ s′ , Rs , s′ ∎ , refl ⟩ , ( _ ⊢ st) , s , refl , refl , refl , px
traceRs◃ (_ , init , (s ⟨ LocalStep st ⟩←— tr)) (there trP)
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◃ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ LocalStep st ⟩←— tr⟪) , refl ⟩ , p
traceRs◃ (_ , init , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◃ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr⟪) , refl ⟩ , p
traceRs◃ (_ , init , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs◃ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr⟪) , refl ⟩ , p

traceRs▷ :  ∀ (Rs : Reachable s){P} →
  (trP : Rs ∋⋯ P) →
  ────────────────────────────────────────────────
  Σ (TraceExtension Rs) (λ trE → intState trE ▷ P)
traceRs▷ (_ , init , (s ⟨ Deliver tpm∈ ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ Deliver tpm∈ ⟩←— tr⟪) , refl ⟩ , p
traceRs▷ (_ , init , (s′ ⟨ LocalStep st ∣ s ⟩←— tr)) (here px)   =
  ⟨ s , (_ , init , tr) , (s′ ⟨ LocalStep st ⟩←— s ∎) , refl ⟩ , ( _ ⊢ st) , refl , refl , px
traceRs▷ (_ , init , (s ⟨ LocalStep st     ⟩←— tr)) (there trP)
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ LocalStep st ⟩←— tr⟪) , refl ⟩ , p
traceRs▷ (_ , init , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr⟪) , refl ⟩ , p
traceRs▷ (_ , init , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr)) trP
  with ⟨ s⟪ , Rs⟪ , tr⟪ , refl ⟩ , p ← traceRs▷ (_ , init , tr) trP
  = ⟨ s⟪ , Rs⟪ , (s ⟨ WaitUntil t <Δ now≤t ⟩←— tr⟪) , refl ⟩ , p

-- TODO: traceRs ⇒ non-empty extension (traceRs⁺)

-- _≺_ : S → S → Type where
--   ∼ non-reflexive transitive closure
--
--   s′ ⁺↞— s
--   ────────
--   s ≺ s′

-- eventually: ≺-rec (traceRs⁺ st-proposes) Rs′ ...

∃→ : Type
∃→ = ∃ λ s → ∃ λ s′ → s —→ s′

data IsLocal : ∃→ → Type where
  LocalStep : ∀ ⦃ _ : Honest p ⦄ {st : p ⦂ s .currentTime ⊢ s ＠ p — menv —→ ls′} →
    IsLocal (s , -, LocalStep st)

record _ᴸ←—_ (s′ s : GlobalState) : Type where
  constructor _⊣ᴸ_
  field {_p _menv _ls′} : _
        ⦃ hp ⦄ : Honest _p
  _ls  = s ＠ _p
  field localStep : _p ⦂ s .currentTime ⊢ _ls — _menv —→ _ls′
        s≡        : s′ ≡ broadcast (s .currentTime) _menv (s ＠ _p ≔ _ls′)

open _ᴸ←—_

instance
  Dec-IsLocal : IsLocal ⁇¹
  Dec-IsLocal {_ , _ , st} .dec with st
  ... | LocalStep _            = yes LocalStep
  ... | DishonestLocalStep _ _ = no λ ()
  ... | Deliver _              = no λ ()
  ... | WaitUntil _ _ _        = no λ ()

Local→Global : s′ ᴸ←— s → s′ ¹←— s
Local→Global st
  = subst (_¹←— _) (sym $ st .s≡)
  $ LocalStep (st . localStep)

Local→Global⇒IsLocal : ∀ {st : s′ ᴸ←— s} →
  IsLocal (-, -, Local→Global st)
Local→Global⇒IsLocal {st = _ ⊣ᴸ refl} = LocalStep

record ∃IsLocal : Type where
  constructor _,_
  field stl : ∃→
        .loc : IsLocal stl

∃IsLocal≡ : ∀ {r r′} →
  r .∃IsLocal.stl ≡ r′ .∃IsLocal.stl
  ──────────────────
  r ≡ r′
∃IsLocal≡ refl = refl

module _ (r : ∃IsLocal) (let stl , loc = r) where
  getLoc : IsLocal stl
  getLoc = recompute dec loc

  getP : Pid
  getP with stl | getLoc
  ... | _ , _ , LocalStep {p = p} _ | LocalStep = p

  getM : Maybe Envelope
  getM with stl | getLoc
  ... | _ , _ , LocalStep {menv = menv} _ | LocalStep = menv

  getL : LocalState
  getL with stl | getLoc
  ... | _ , _ , LocalStep {ls′ = ls′} _ | LocalStep = ls′

getP≡ : ∀ (st : s′ ᴸ←— s) →
  getP ((-, -, Local→Global st) , Local→Global⇒IsLocal) ≡ st ._p
getP≡ (_ ⊣ᴸ refl) = refl

getM≡ : ∀ (st : s′ ᴸ←— s) →
  getM ((-, -, Local→Global st) , Local→Global⇒IsLocal) ≡ st ._menv
getM≡ (_ ⊣ᴸ refl) = refl

getL≡ : ∀ (st : s′ ᴸ←— s) →
  getL ((-, -, Local→Global st) , Local→Global⇒IsLocal) ≡ st ._ls′
getL≡ (_ ⊣ᴸ refl) = refl

Local→Global-inj : ∀ (st st′ : s′ ᴸ←— s) →
  Local→Global st ≡ Local→Global st′
  ──────────────────────────────────
  st ≡ st′
Local→Global-inj {s′}{s} st@(_ ⊣ᴸ s≡) st′@(_ ⊣ᴸ s≡′) st≡ = QED
  where
  ∃st ∃st′ : ∃→
  ∃st  = -, -, Local→Global st
  ∃st′ = -, -, Local→Global st′

  ∃st≡ : ∃st ≡ ∃st′
  ∃st≡ = cong (λ ◆ → s , s′ , ◆) st≡

  ∃stl ∃stl′ : ∃IsLocal
  ∃stl  = ∃st  , Local→Global⇒IsLocal
  ∃stl′ = ∃st′ , Local→Global⇒IsLocal

  ∃stl≡ : ∃stl ≡ ∃stl′
  ∃stl≡ = ∃IsLocal≡ ∃st≡

  p≡ : st ._p ≡ st′ ._p
  p≡ = subst (_≡ _) (getP≡ st) $ subst (_ ≡_) (getP≡ st′)
     $ cong getP ∃stl≡

  m≡ : st ._menv ≡ st′ ._menv
  m≡ = subst (_≡ _) (getM≡ st) $ subst (_ ≡_) (getM≡ st′)
     $ cong getM ∃stl≡

  l≡ : st ._ls′ ≡ st′ ._ls′
  l≡ = subst (_≡ _) (getL≡ st) $ subst (_ ≡_) (getL≡ st′)
     $ cong getL ∃stl≡

  QED : st ≡ st′
  QED with st ._p ≟ st′ ._p
  ... | no p≢ = ⊥-elim $ p≢ p≡
  ... | yes refl with st ._menv ≟ st′ ._menv
  ... | no m≢ = ⊥-elim $ m≢ m≡
  ... | yes refl with st ._ls′ ≟ st′ ._ls′
  ... | no l≢ = ⊥-elim $ l≢ l≡
  ... | yes refl with ⟫ s≡ | ⟫ s≡′ | ⟫ st≡
  ... | ⟫ refl | ⟫ refl | ⟫ refl = refl

_⟨_⟩←—ᴿ_ : ∀ s′ → s′ ¹←— s → Reachable s → Reachable s′
_ ⟨ st ⟩←—ᴿ (_ , s-init , tr) =
  (_ , s-init , (_ ⟨ st ⟩←— tr))

record TraceExtension⁺ {z} (Rz : Reachable z) : Type where
  constructor ⟨_,_,_,_⟩
  field
    {x y} : GlobalState
    Rx    : Reachable x
    y←x   : y ᴸ←— x
    z↞y   : z ↞— y

  y¹←x : y ¹←— x
  y¹←x = Local→Global y←x

  z↞x : z ↞— x
  z↞x = _ `—→⟨ y¹←x ⟩ z↞y

  Ry : Reachable y
  Ry = _ ⟨ y¹←x ⟩←—ᴿ Rx

  field
    Rz≡ : Rz ≡ extendRs Ry z↞y
    -- Rz≡ : Rz ≡ extendRs Rx z↞x

  step : Step
  step = _ ⊢ y←x ._ᴸ←—_.localStep

open TraceExtension⁺

private
  UIP : (p q : s ≡ s′) → p ≡ q
  UIP refl refl = refl

  open Prod hiding (,-injectiveʳ)

step≡-TE⁺ : ∀ {s} (Rs : Reachable s) (trE trE′ : TraceExtension⁺ Rs) →
  _≡_ {A = ∃ λ x → ∃ λ y → y ¹←— x} (-, -, y¹←x trE) (-, -, y¹←x trE′)
  ────────────────────────────────────────────────────────────────────
  step trE ≡ step trE′
step≡-TE⁺ Rs trE trE′ eq
  with refl ← ,-injectiveˡ eq
  with refl ← ,-injectiveˡ $ ,-injectiveʳ-≡ UIP eq refl
  with eq′  ← ,-injectiveʳ-≡ UIP (,-injectiveʳ-≡ UIP eq refl) refl
  with refl ← Local→Global-inj _ _ eq′
  = refl

traceRs⁺ : ∀ (Rs : Reachable s) {P} →
  (trP : Rs ∋⋯ P) →
  ────────────────────────────────
  Σ (TraceExtension⁺ Rs) (P ∘ TraceExtension⁺.step)
traceRs⁺ (_ , init , (s ⟨ Deliver tpm∈ ⟩←— tr)) trP
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ Deliver tpm∈ ⟩←— tr) , refl ⟩ , P
traceRs⁺ (_ , init , (s′ ⟨ LocalStep st ∣ s ⟩←— tr)) (here px)
 = ⟨ (_ , init , tr) , (st ⊣ᴸ refl) , (s′ ∎) , refl ⟩ , px
traceRs⁺ (_ , init , (_ ⟨ LocalStep  st ⟩←— tr)) (there trP)
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ LocalStep st ⟩←— tr) , refl ⟩ , P
traceRs⁺ (_ , init , (_ ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr)) trP
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ DishonestLocalStep {env = env} ¬hp st ⟩←— tr) , refl ⟩ , P
traceRs⁺ (_ , init , (_ ⟨ WaitUntil t <Δ now≤t ⟩←— tr)) trP
  with ⟨ s , Rs , tr , refl ⟩ , P ← traceRs⁺ (_ , init , tr) trP
     = ⟨ s , Rs , (_ ⟨ WaitUntil t <Δ now≤t ⟩←— tr) , refl ⟩ , P

{-
TraceExtension⁺⁻ : ∀ {Rs : Reachable s} → TraceExtension⁺ Rs → TraceExtension Rs
TraceExtension⁺⁻ tr@(⟨ Rs , st , sts , refl ⟩) =
  ⟨ tr .x , Rs , _ `—→⟨ Local→Global st ⟩ sts  , refl ⟩

TraceExtension⁺⁻⁺ : ∀ {Rs : Reachable s} → TraceExtension⁺ Rs → TraceExtension Rs
TraceExtension⁺⁻⁺ tr@(⟨ Rs , st@(_ ⊣ᴸ eq) , sts , refl ⟩) =
  ⟨ tr .y , _ ⟨ Local→Global st ⟩←—ᴿ Rs , sts  , {!refl!} ⟩
-}

factorRs : ∀ (Rs : Reachable s)
  (trE₁ trE₂ : TraceExtension Rs) →
  ─────────────────────────────────────
  let s₁ = trE₁ .intState
      s₂ = trE₂ .intState
  in (s₁ ↞— s₂) ⊎ (s₂ ↞— s₁)
factorRs Rs
  ⟨ s₁ , (_ , _ , tr₁) , ext₁ , refl ⟩
  ⟨ s₂ , (_ , _ , tr₂) , ext₂ , eq₂ ⟩
  with refl ← cong proj₁ eq₂
  = factor tr₁ ext₁ tr₂ ext₂ (Reachable-inj eq₂)

open import Data.Product.Properties.WithK using (,-injectiveʳ)

factorRs⁺ : ∀ (Rs : Reachable s) → let open TraceExtension⁺ in
  (tr tr′ : TraceExtension⁺ Rs) →
  ────────────────────────────
    (step tr ≡ step tr′)
  ⊎ (tr′ .x ↞— tr  .y)
  ⊎ (tr  .x ↞— tr′ .y)
factorRs⁺ Rs
  trE@(⟨ (_ , init , tr)  , (st  ⊣ᴸ refl) , st∗  , refl ⟩)
  trE′@(⟨ (_ , _   , tr′) , (st′ ⊣ᴸ refl) , st∗′ , eq₃ ⟩)
  with refl ← cong proj₁ eq₃
  with refl ← cong proj₁ $ ,-injectiveʳ eq₃
  with eq   ← ,-injectiveʳ  $ ,-injectiveʳ eq₃
  with factor⁺ tr (y¹←x trE) st∗ tr′ (y¹←x trE′) st∗′
               (Reachable-inj $ cong (_ ,_) $ cong (init ,_) eq)
... | inj₁ st≡      = inj₁ $ step≡-TE⁺ Rs trE trE′ st≡
... | inj₂ (inj₁ P) = inj₂ $ inj₂ P
... | inj₂ (inj₂ P) = inj₂ $ inj₁ P
