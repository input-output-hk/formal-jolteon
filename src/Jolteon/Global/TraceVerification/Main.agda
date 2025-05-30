
module Jolteon.Global.TraceVerification.Main where

open import Prelude
import IO.Primitive.Core as IO
open IO using (IO)
import IO.Primitive.Finite as IO

open import Jolteon.Global.TraceVerification.Assumptions
import Jolteon.Global.TraceVerification as Verify

module Run params = Verify (⋯ params)

main : IO ⊤
main = IO.putStrLn "Verifying trace... INTERNAL SERVER ERROR: 500"
