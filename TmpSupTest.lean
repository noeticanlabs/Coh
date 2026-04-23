/-!
## Quick Sup and Cost Test
-/

import Coh.V2.FiniteWord
import Mathlib.Data.Real.NNReal

open Coh.V2.FiniteWord

-- Simple alphabet
inductive A | x deriving DecidableEq, Fintype, Repr
inductive B | y deriving DecidableEq, Fintype, Nonempty, Repr

def cb : B → NNreal := fun _ => 5

def sys := mkFiniteWordSystem (A := A) (B := B) cb

def my_trace : HiddenG A B := [(.x, .y), (.x, .y)]

#eval hiddenCost cb my_trace -- Expected: 10
#eval c_max cb              -- Expected: 5

example : hiddenCost cb my_trace = 10 := rfl
example : c_max cb = 5 := rfl
