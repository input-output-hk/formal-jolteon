
module Jolteon.Global.TraceVerification.Examples where

open import Prelude
open import Prelude.Result
open import Jolteon.Traces.Core
open import Jolteon.Global.TraceVerification ⋯
open import Jolteon.Global.TraceVerification.LocalStep ⋯
open import Jolteon.Traces.Trace00
open import Jolteon.Traces.Trace00b
open import Jolteon.Traces.Trace01
open import Jolteon.Traces.Trace01b
open import Jolteon.Traces.Trace02
open import Jolteon.Traces.Trace03
open import Jolteon.Traces.Trace04
open import Jolteon.Traces.LockFuture

roundTrip : (tr : s —↠ s′) → Result _ (ValidTrace (eraseTrace tr) s)
roundTrip {s} tr = verifyTrace (eraseTrace tr) s

opaque
  unfolding trace00 trace00b trace01 trace01b trace02 trace03 trace04 lockFuture

  test00 : IsOk (roundTripTrace trace00)
  test00 = _

  test00b : IsOk (roundTripTrace trace00b)
  test00b = _

  test01 : IsOk (roundTripTrace trace01)
  test01 = _

  test01b : IsOk (roundTripTrace trace01b)
  test01b = _

  test02 : IsOk (roundTripTrace trace02)
  test02 = _

  test03 : IsOk (roundTripTrace trace03)
  test03 = _

  test04 : IsOk (roundTripTrace trace04)
  test04 = _

  testLockFuture : IsOk (roundTripTrace lockFuture)
  testLockFuture = _
