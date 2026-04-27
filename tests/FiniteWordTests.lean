import Coh.V2.FiniteWord
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
## Finite-Word Model Tests
-/

open Coh.V2.FiniteWord

-- Define a simple alphabet
inductive Alpha | a | b deriving DecidableEq, Fintype, Nonempty, Repr
inductive HiddenAlpha | h1 | h2 deriving DecidableEq, Fintype, Nonempty, Repr

-- Define a cost function for hidden symbols using ℚ
def my_c_B : HiddenAlpha → ℚ
| .h1 => 1
| .h2 => 2

instance : HasPositiveCost HiddenAlpha my_c_B := ⟨⟨HiddenAlpha.h1, by simp [my_c_B]⟩⟩
instance : HasNonnegativeCost HiddenAlpha my_c_B := ⟨by intro b; cases b <;> simp [my_c_B]⟩

-- Instantiate the system
def my_sys := (mkFiniteWordSystem (A := Alpha) (B := HiddenAlpha) my_c_B).1

-- Example traces
def t1 : HiddenG Alpha HiddenAlpha := [(.a, .h1), (.b, .h2)]
def t2 : HiddenG Alpha HiddenAlpha := [(.a, .h2)]

#eval hiddenCost Alpha HiddenAlpha my_c_B t1 -- Expected: 3
#eval proj t1             -- Expected: [.a, .b]
#eval c_max my_c_B        -- Expected: 2

-- Verify cost bound
example : hiddenCost Alpha HiddenAlpha my_c_B t1 ≤ (t1.length : ℚ) * (c_max my_c_B : ℚ) := by
  native_decide

-- Verify composition
def t12 := hComp t1 t2
#eval t12 -- Expected: some [(.a, .h1), (.b, .h2), (.a, .h2)]
