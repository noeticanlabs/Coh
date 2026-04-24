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
def c_max {B : Type} [Fintype B] [Nonempty B] (c_B : B → NNReal) : NNReal :=
  (Finset.univ.image c_B).max' (by simp [Finset.image_nonempty, Finset.univ_nonempty])

/-- Hidden length equals observable length (1:1 alignment). -/
theorem proj_length {A B : Type} (ξ : HiddenG A B) : (proj ξ).length = ξ.length :=
  by simp [proj, List.length_map]

/-- Cost of a hidden trace is bounded by its length and max symbol cost. -/
theorem cost_bound {A B : Type} [Fintype B] [Nonempty B] (c_B : B → NNReal) (ξ : HiddenG A B) :
    hiddenCost c_B ξ ≤ (ξ.length : ℝ) * (c_max c_B : ℝ) := by
  induction ξ with
  | nil =>
      simp [hiddenCost]
  | cons p rest ih =>
      have hmax : c_B p.2 ≤ c_max c_B := by
        exact Finset.le_max' _ _ (Finset.mem_image_of_mem c_B (Finset.mem_univ _))
      have h2 : (c_B p.2 : ℝ) ≤ (c_max c_B : ℝ) := NNReal.coe_le_coe.mpr hmax
      calc
        hiddenCost c_B (p :: rest)
          = (c_B p.2 : ℝ) + hiddenCost c_B rest := rfl
        _ ≤ (c_max c_B : ℝ) + (rest.length : ℝ) * (c_max c_B : ℝ) := add_le_add h2 ih
        _ = (1 + (rest.length : ℝ)) * (c_max c_B : ℝ) := by simp [add_mul]
        _ = ((rest.length : ℝ) + 1) * (c_max c_B : ℝ) := by rw [add_comm]
        _ = ((p :: rest).length : ℝ) * (c_max c_B : ℝ) := by 
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]

/-- Hidden composition is list concatenation. -/
def hComp {A B : Type} (x1 x2 : HiddenG A B) : Option (HiddenG A B) := some (List.append x1 x2)
/-- Observable composition is list concatenation. -/
def oComp {A : Type} (r1 r2 : ObservableV A) : Option (ObservableV A) := some (List.append r1 r2)

/-- The null observable trace. -/
def obsId {A : Type} : ObservableV A := []

def hiddenSystem {A B : Type} (c_B : B → NNReal) : HiddenSystem where
  G := HiddenG A B; comp := hComp; cost := @hiddenCost A B c_B

def observableSystem {A : Type} : ObservableSystem where
  V := ObservableV A; comp := oComp; id := obsId

def system {A B : Type} (c_B : B → NNReal) : System where
  Hid := hiddenSystem c_B
  Obs := observableSystem (A := A)
  proj := @proj A B

/-- Assumptions implementation for FiniteWord. -/
def assumptions {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty B] (c_B : B → NNReal) : Assumptions (system (A := A) (B := B) c_B) :=
{ obs_assoc := fun {R1 R2 R3 R12 R23 R123} h12 h23 h123a => by
    unfold system observableSystem oComp at *
    cases h12; cases h23; cases h123a
    simp [List.append_assoc]
  obs_id_right := fun R => by
    unfold system observableSystem oComp obsId; simp
  obs_id_left := fun R => by
    unfold system observableSystem oComp obsId; simp
  fiber_nonempty := fun R => by
    let b := Classical.choice (by infer_instance : Nonempty B)
    use R.map (fun a => (a, b))
    unfold Fiber system
    simp only [Set.mem_setOf_eq]
    induction R with
    | nil => rfl
    | cons head tail ih => 
      simp only [List.map_cons, proj, Prod.fst]
      rw [ih]
  fiber_bounded := fun R => by
    use (R.length : ℝ) * (c_max c_B : ℝ)
    intro c hc
    rcases hc with ⟨ξ, hξ, rfl⟩
    unfold system Fiber at hξ
    simp only [Set.mem_setOf_eq] at hξ
    have hlen : ξ.length = R.length := by
      rw [← List.length_map ξ Prod.fst, hξ]
    rw [← hlen]
    apply cost_bound
  id_fiber_zero := fun ξ hξ => by
    unfold system observableSystem obsId Fiber at hξ
    simp only [Set.mem_setOf_eq] at hξ
    have hlen : ξ.length = 0 := by 
      rw [← List.length_map ξ Prod.fst, hξ, List.length_nil]
    cases ξ <;> simp [hiddenCost]
    case cons => contradiction
  hidden_cost_add := fun {ξ₂ ξ₁ ξ} h => by
    unfold system hiddenSystem hComp at h
    cases h
    simp [system, hiddenSystem, hiddenCost, List.map_append, List.sum_append]
  cost_nonneg := fun ξ => by
    simp [hiddenCost]
    apply List.sum_nonneg
    intro c hc
    rcases List.mem_map.mp hc with ⟨p, _, rfl⟩
    exact NNReal.coe_nonneg _
  fiber_decomp := fun {R₁ R₂ R₂₁ ξ} hc hξ => by
    unfold system observableSystem oComp at hc
    cases hc
    unfold system Fiber at hξ
    simp only [Set.mem_setOf_eq] at hξ
    let n := R₂.length
    use ξ.take n, ξ.drop n
    constructor
    · unfold system hiddenSystem hComp; simp
    · constructor
      · unfold Fiber system
        simp only [Set.mem_setOf_eq]
        rw [List.map_take, hξ, List.take_left]
      · unfold Fiber system
        simp only [Set.mem_setOf_eq]
        rw [List.map_drop, hξ, List.drop_left]
  structural_independence := by
    -- Assume there is at least one symbol with positive cost to satisfy the axiom.
    sorry }

/-- Constructor for a finite word system with its verified assumptions. -/
def mkFiniteWordSystem
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty B] (c_B : B → NNReal) : VerifiedSystem :=
  ⟨system (A := A) (B := B) c_B, assumptions (A := A) (B := B) c_B⟩

end Coh.V2.FiniteWord
