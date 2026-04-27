import Coh.V2.FiniteWord
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Coh.V2.FiniteWord

-- Simple alphabet
inductive A | x deriving DecidableEq, Fintype, Nonempty, Repr
inductive B | y deriving DecidableEq, Fintype, Nonempty, Repr

def cb : B → ℚ := fun _ => 5

instance : HasPositiveCost B cb := ⟨⟨B.y, by simp [cb]⟩⟩
instance : HasNonnegativeCost B cb := ⟨by intro b; cases b; simp [cb]⟩

def sys := mkFiniteWordSystem (A := A) (B := B) cb

def my_trace : HiddenG A B := [(.x, .y), (.x, .y)]

#eval hiddenCost A B cb my_trace -- Expected: 10
#eval c_max cb              -- Expected: 5

example : hiddenCost A B cb my_trace = 10 := by native_decide
example : c_max cb = 5 := by native_decide

def main : IO Unit := do
  IO.println "FiniteWordTests: Hidden cost and c_max verified."
