/-!
## Finite-Word Model Tests

This file contains concrete examples and tests for the Finite-Word model implementation.
-/

import Coh.V2.FiniteWord
import Mathlib.Data.Real.NNReal

open Coh.V2.FiniteWord

-- Define a simple alphabet
inductive Alpha | a | b deriving DecidableEq, Fintype, Repr
inductive HiddenAlpha | h1 | h2 deriving DecidableEq, Fintype, Nonempty, Repr

-- Define a cost function for hidden symbols
def my_c_B : HiddenAlpha → NNreal
| .h1 => 1
| .h2 => 2

-- Instantiate the system
def my_sys := (mkFiniteWordSystem (A := Alpha) (B := HiddenAlpha) my_c_B).1

-- Example traces
def t1 : HiddenG Alpha HiddenAlpha := [(.a, .h1), (.b, .h2)]
def t2 : HiddenG Alpha HiddenAlpha := [(.a, .h2)]

#eval hiddenCost my_c_B t1 -- Expected: 3
#eval proj t1             -- Expected: [.a, .b]
#eval c_max my_c_B        -- Expected: 2

-- Verify cost bound
example : hiddenCost my_c_B t1 ≤ (t1.length : ℝ) * (c_max my_c_B : ℝ) := by
  native_decide

-- Verify composition
def t12 := hComp t1 t2
#eval t12 -- Expected: some [(.a, .h1), (.b, .h2), (.a, .h2)]
