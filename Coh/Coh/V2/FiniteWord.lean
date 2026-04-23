import Coh.V2.Primitive
import Coh.V2.Definitions
import Coh.V2.Axioms
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Fintype.Basic

/-!
## Coh V2 Finite-Word Model

This module implements a concrete Coh V2 system based on finite alphabets
and list-based traces. It provides hidden and observable layers where
costs are additive over hidden symbols.
-/

noncomputable section

namespace Coh.V2.FiniteWord

/-- The set of hidden traces (pairs of observable and hidden symbols). -/
def HiddenG (A B : Type) : Type := List (A × B)
/-- The set of observable traces (lists of observable symbols). -/
def ObservableV (A : Type) : Type := List A

/-- Projection from hidden to observable layer by dropping hidden tags. -/
def proj {A B : Type} (ξ : HiddenG A B) : ObservableV A := ξ.map Prod.fst

/-- Exact cost of a hidden trace, summed over hidden tags. -/
def hiddenCost {A B : Type} (c_B : B → NNReal) (ξ : HiddenG A B) : ℝ :=
  (ξ.map (fun p => (c_B p.2 : ℝ))).sum

/-- The maximum cost of a single hidden symbol. -/
def c_max {B : Type} [Fintype B] (c_B : B → NNReal) : NNReal := 
  (Finset.univ.image c_B).max' (by simp [Finset.image_nonempty, Finset.univ_nonempty])

/-- Hidden length equals observable length (1:1 alignment). -/
theorem proj_length {A B : Type} (ξ : HiddenG A B) : (proj ξ).length = ξ.length :=
  by simp [proj, List.length_map]

/-- Cost of a hidden trace is bounded by its length and max symbol cost. -/
theorem cost_bound {A B : Type} [Fintype B] (c_B : B → NNReal) (ξ : HiddenG A B) : 
    hiddenCost c_B ξ ≤ (ξ.length : ℝ) * (c_max c_B : ℝ) := by
  induction ξ with
  | nil => simp [hiddenCost]
  | cons p rest ih =>
    simp [hiddenCost]
    have h : c_B p.2 ≤ c_max c_B := Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    calc (c_B p.2 : ℝ) + (rest.map (fun p => (c_B p.2 : ℝ))).sum
      _ ≤ (c_max c_B : ℝ) + (rest.length : ℝ) * (c_max c_B : ℝ) := add_le_add (NNReal.coe_le_coe.mpr h) ih
      _ = (1 + (rest.length : ℝ)) * (c_max c_B : ℝ) := by ring
      _ = (rest.length + 1) * (c_max c_B : ℝ) := by rw [add_comm]

/-- Hidden composition is list concatenation. -/
def hComp {A B : Type} (x1 x2 : HiddenG A B) : Option (HiddenG A B) := some (x1 ++ x2)
/-- Observable composition is list concatenation. -/
def oComp {A : Type} (r1 r2 : ObservableV A) : Option (ObservableV A) := some (r1 ++ r2)

/-- The null observable trace. -/
def obsId {A : Type} : ObservableV A := []

def hiddenSystem {A B : Type} (c_B : B → NNReal) : HiddenSystem where
  G := HiddenG A B; comp := hComp; cost := hiddenCost c_B

def observableSystem {A : Type} : ObservableSystem where
  V := ObservableV A; comp := oComp; id := obsId

def system {A B : Type} (c_B : B → NNReal) : System where
  Hid := hiddenSystem c_B; Obs := observableSystem; proj := proj

/-- Assumptions implementation for FiniteWord. -/
def assumptions {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty B] (c_B : B → NNReal) : Assumptions (system c_B) :=
{ obs_assoc := fun {R1 R2 R3 R12 R23 R123} h12 h23 h312 => by
    simp [oComp] at *
    rw [← h12, ← h23, ← h312]
    apply List.append_assoc
  obs_id_right := fun R => by simp [oComp]
  obs_id_left := fun R => by simp [oComp]
  fiber_nonempty := fun R => by
    let b0 := Classical.choice (by infer_instance : Nonempty B)
    use R.map fun a => (a, b0)
    simp [proj, system, hiddenSystem, observableSystem]
  fiber_bounded := fun R => by
    use (R.length : ℝ) * (c_max c_B : ℝ)
    intro c hx
    rcases hx with ⟨ξ, hξ, rfl⟩
    calc (hiddenCost c_B ξ) ≤ (ξ.length : ℝ) * (c_max c_B : ℝ) := cost_bound c_B ξ
      _ = ((proj ξ).length : ℝ) * (c_max c_B : ℝ) := by rw [proj_length]
      _ = (R.length : ℝ) * (c_max c_B : ℝ) := by rw [hξ]
  id_fiber_zero := fun ξ hξ => by
    cases ξ; rfl
    simp [Fiber, proj, system, observableSystem, obsId] at hξ
    contradiction
  hidden_cost_add := fun {x2 x1 x} h => by
    simp [hComp] at h; rw [← h]
    simp [hiddenCost, List.map_append, List.sum_append]
  fiber_decomp := fun {R1 R2 R21 ξ} hc h => by
    simp [oComp] at hc
    injection hc with h_append
    subst h_append
    simp [Fiber, proj, system, observableSystem] at h
    let s := ξ.splitAt R2.length
    use s.1, s.2
    constructor
    · simp [hComp, List.take_append_drop]
    · constructor
      · simp [Fiber, proj, h]
        rw [List.map_take, List.take_map, h, List.take_left_append]
      · simp [Fiber, proj, h]
        rw [List.map_drop, List.drop_map, h, List.drop_left_append] }

/-- Structure to package a system and its verified assumptions. -/
structure VerifiedSystem where
  sys : System
  asm : Assumptions sys

/-- Constructor for a finite word system with its verified assumptions. -/
def mkFiniteWordSystem
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty B] (c_B : B → NNReal) : VerifiedSystem :=
  ⟨system c_B, assumptions (A := A) (B := B) c_B⟩

end Coh.V2.FiniteWord
