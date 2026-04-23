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

namespace Coh.V2

/-
## Finite-Word Model

Hidden G = List (A × B), Observable V = List A.
Projection drops hidden refinement, cost sums over hidden.
-/

section
  variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  variable (c_B : B → NNReal)
  variable [nonempty_B : Nonempty B]

  /-- The set of hidden traces (pairs of observable and hidden symbols). -/
  def HiddenG : Type := List (A × B)
  /-- The set of observable traces (lists of observable symbols). -/
  def ObservableV : Type := List A

  /-- Projection from hidden to observable layer by dropping hidden tags. -/
  def proj (ξ : HiddenG) : ObservableV := ξ.map Prod.fst

  /-- Exact cost of a hidden trace, summed over hidden tags. -/
  def hiddenCost (ξ : HiddenG) : ℝ :=
    (ξ.map (fun p => (c_B p.2 : ℝ))).sum

  /-- The maximum cost of a single hidden symbol. -/
  def c_max : NNReal := (Finset.univ.image c_B).max' (by simp [Finset.image_nonempty, Finset.univ_nonempty])

  /-- Hidden length equals observable length (1:1 alignment). -/
  theorem proj_length (ξ : HiddenG) : (proj ξ).length = ξ.length :=
    by simp [proj, List.length_map]

  /-- Cost of a hidden trace is bounded by its length and max symbol cost. -/
  theorem cost_bound (ξ : HiddenG) : hiddenCost c_B ξ ≤ (ξ.length : ℝ) * (c_max c_B : ℝ) := by
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
  def hComp (x1 x2 : HiddenG) : Option HiddenG := some (x1 ++ x2)
  /-- Observable composition is list concatenation. -/
  def oComp (r1 r2 : ObservableV) : Option ObservableV := some (r1 ++ r2)

  /-- The null observable trace. -/
  def obsId : ObservableV := []

  def hiddenSystem : HiddenSystem where
    G := HiddenG; comp := hComp; cost := hiddenCost c_B

  def observableSystem : ObservableSystem where
    V := ObservableV; comp := oComp; id := obsId

  def system : System where
    Hid := hiddenSystem; Obs := observableSystem; proj := proj

end

section
  variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  variable (c_B : B → NNReal)
  variable [nonempty_B : Nonempty B]

  local notation "S" => system c_B

  theorem obs_assoc :
    ∀ {R₁ R₂ R₃ R₁₂ R₂₃ R₁₂₃ : ObservableV},
      oComp R₂ R₁ = some R₁₂ →
      oComp R₃ R₂ = some R₂₃ →
      oComp R₃ R₁₂ = some R₁₂₃ →
      oComp R₂₃ R₁ = some R₁₂₃ := by
    intro R1 R2 R3 R12 R23 R123 h12 h23 h312
    simp [oComp] at *
    rw [← h12, ← h23, ← h312]
    apply List.append_assoc

  theorem obs_id_right (R : ObservableV) : oComp R [] = some R := by simp [oComp]
  theorem obs_id_left (R : ObservableV) : oComp [] R = some R := by simp [oComp]

  /-- Every observable trace has a hidden witness (by mapping to a default hidden symbol). -/
  theorem fiber_nonempty (R : ObservableV) : (Fiber (system c_B) R).Nonempty := by
    let b0 := Classical.choice nonempty_B
    use R.map fun a => (a, b0)
    simp [proj, system, hiddenSystem, observableSystem]

  /-- Fiber cost sets are bounded by the max cost. -/
  theorem fiber_bounded (R : ObservableV) : BddAbove (CostSet (system c_B) R) := by
    use (R.length : ℝ) * (c_max c_B : ℝ)
    intro c hx
    rcases hx with ⟨ξ, hξ, rfl⟩
    calc (hiddenCost c_B ξ) ≤ (ξ.length : ℝ) * (c_max c_B : ℝ) := cost_bound c_B ξ
      _ = ((proj ξ).length : ℝ) * (c_max c_B : ℝ) := by rw [proj_length]
      _ = (R.length : ℝ) * (c_max c_B : ℝ) := by rw [hξ]

  theorem id_fiber_zero : ∀ ξ ∈ Fiber (system c_B) [], (hiddenCost c_B ξ) = 0 := by
    intro ξ h; cases ξ; rfl
    simp [Fiber, proj] at h; contradiction

  /-- Exact cost additivity for finite word systems. -/
  theorem hidden_cost_add {x2 x1 x : HiddenG} (h : hComp x2 x1 = some x) :
      hiddenCost c_B x = hiddenCost c_B x2 + hiddenCost c_B x1 := by
    simp [hComp] at h; rw [← h]
    simp [hiddenCost, List.map_append, List.sum_append]

  /-- Splitting a composite observable witness into component hidden witnesses. -/
  theorem fiber_decomp {R1 R2 R21 : ObservableV} {ξ : HiddenG} (hc : oComp R2 R1 = some R21)
      (h : ξ ∈ Fiber (system c_B) R21) :
      ∃ ξ₂ ξ₁, hComp ξ₂ ξ₁ = some ξ ∧ ξ₂ ∈ Fiber (system c_B) R2 ∧ ξ₁ ∈ Fiber (system c_B) R1 := by
    simp [oComp] at hc; subst hc
    simp [Fiber, proj] at h
    let s := ξ.splitAt R1.length
    use s.2, s.1
    constructor
    · simp [hComp, List.take_append_drop]
    · constructor
      · simp [Fiber, proj, h]
        rw [List.map_drop, List.drop_map, h, List.drop_left_append]
      · simp [Fiber, proj, h]
        rw [List.map_take, List.take_map, h, List.take_left_append]

  /-- The assumption set for a finite word system. -/
  def assumptions : Assumptions (system c_B) :=
  { obs_assoc := obs_assoc c_B,
    obs_id_right := obs_id_right,
    obs_id_left := obs_id_left,
    fiber_nonempty := fiber_nonempty c_B,
    fiber_bounded := fiber_bounded c_B,
    id_fiber_zero := id_fiber_zero c_B,
    hidden_cost_add := hidden_cost_add c_B,
    fiber_decomp := fiber_decomp c_B }

end

/-- Constructor for a finite word system with its verified assumptions. -/
def mkFiniteWordSystem
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty B] (c_B : B → NNReal) :
    Σ (S : System), Assumptions S :=
  ⟨system c_B, assumptions c_B⟩

end Coh.V2
