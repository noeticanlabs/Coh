import Coh.V1.Coh
import Coh.V2.Primitive
import Coh.V2.Definitions
import Coh.V2.Axioms
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
## Coh V1 to V2 Bridge

This module defines the mapping from the V1 Operational Trace model
to the V2 Categorical system.
-/

namespace Coh.V1

open V2

/-- Observable projection: maps a sequence of steps to their source states. -/
def stepsObs {X : Type} (ss : List (Step X)) : List X :=
  ss.map Step.src

/-- A hidden system based on V1 operational steps. -/
def hiddenSystem (X : Type) [DecidableEq X] : HiddenSystem where
  G := List (Step X)
  comp := fun L1 L2 => some (L1 ++ L2)
  cost := fun L => stepsSpend L

/-- An observable system based on V1 operational traces. -/
def observableSystem (X : Type) [DecidableEq X] : ObservableSystem where
  V := List X
  comp := fun L1 L2 => some (L1 ++ L2)
  id := []
  complexity := fun L => L.length

/-- The V1 to V2 system mapping. -/
def system (X : Type) [DecidableEq X] : System where
  Hid := hiddenSystem X
  Obs := observableSystem X
  proj := stepsObs
  proj_comp := by
    intros ξ₂ ξ₁ ξ h
    simp [hiddenSystem] at h
    subst h
    simp [stepsObs, List.map_append]

/-- Class for types with bounded spend per step. -/
class BoundedSpend (X : Type) where
  c_max : ℚ
  spend_le : ∀ s : Step X, s.costSpend ≤ c_max

/-- Positive spend assumption for V1 states. -/
class HasPositiveSpend (X : Type) where
  positive_spend : ∀ x : X, ∃ step : Step X, step.src = x ∧ step.costSpend > 0

/-- Verification of Assumptions for the V1->V2 bridge. -/
def assumptions (X : Type) [DecidableEq X] [Nonempty X] [BoundedSpend X] [hp : HasPositiveSpend X] : Assumptions (system X) :=
{ obs_assoc := by
    intros R1 R2 R3 R12 R23 R123 h12 h23 h123
    simp [system, observableSystem] at h12 h23 h123
    cases h12; cases h23; cases h123
    simp [List.append_assoc]
  obs_id_right := fun R => by simp [system, observableSystem]
  obs_id_left := fun R => by simp [system, observableSystem]
  fiber_nonempty := by
    intros R
    use R.map (fun x => Step.mk x x (Glyph.mk GlyphTag.invoke "" (ControlToken.mk "" "") True.intro True.intro) 0 0 (by linarith) (by linarith) True.intro True.intro)
    simp [Fiber, system, stepsObs, List.map_map, Function.comp, Step.src]
  fiber_bounded := by
    intros R
    use (R.length : ℚ) * BoundedSpend.c_max X
    intro q hq
    rcases hq with ⟨ξ, hξ, rfl⟩
    simp [Fiber, system, stepsObs] at hξ
    have hlen : ξ.length = R.length := by
      rw [← List.length_map Step.src ξ, hξ]
    simp [hiddenSystem, stepsSpend]
    induction ξ generalizing R
    case nil => simp [stepsSpend]
    case cons hd tl ih =>
      simp [stepsSpend]
      have hmax : hd.costSpend ≤ BoundedSpend.c_max X := BoundedSpend.spend_le hd
      have htl : stepsSpend tl ≤ (tl.length : ℚ) * BoundedSpend.c_max X := by
        apply ih
        simp [stepsObs] at hξ
        exact hξ.2
      calc
        hd.costSpend + stepsSpend tl ≤ BoundedSpend.c_max X + (tl.length : ℚ) * BoundedSpend.c_max X := add_le_add hmax htl
        _ = (1 + (tl.length : ℚ)) * BoundedSpend.c_max X := by rw [add_comm, add_mul, one_mul]
        _ = (hd :: tl : List (Step X)).length * BoundedSpend.c_max X := by simp [List.length]
  id_fiber_zero := by
    intros ξ hξ
    simp [Fiber, system, stepsObs] at hξ
    cases ξ with
    | nil => rfl
    | cons hd tl =>
      have h : stepsObs (hd :: tl) = [] := hξ
      simp [stepsObs] at h
  hidden_cost_add := by
    intros ξ₂ ξ₁ ξ h
    simp [hiddenSystem] at h
    cases h
    simp [hiddenSystem, stepsSpend_append]
  cost_nonneg := fun ξ => stepsSpend_nonneg ξ
  structural_independence := by
    let x := Classical.choice (show Nonempty X from inferInstance)
    rcases hp.positive_spend x with ⟨step, hsrc, hpos⟩
    let R : List X := [x]
    use R
    have h_in_q : step.costSpend ∈ CostSetQ (system X) R := by
      exists [step]
      constructor
      · simp [Fiber, system, stepsObs, hsrc, R]
      · simp [hiddenSystem, stepsSpend]
    have h_in_real : (step.costSpend : ℝ) ∈ CostSetReal (system X) R := by
      exists step.costSpend
    have h_bdd : BddAbove (CostSetReal (system X) R) := by
      use ((R.length : ℚ) * BoundedSpend.c_max X : ℝ)
      intro r hr
      rcases hr with ⟨q, hq, rfl⟩
      rcases hq with ⟨ξ, hξ, rfl⟩
      simp [Fiber, system, stepsObs] at hξ
      have hlen : ξ.length = R.length := by rw [← List.length_map Step.src ξ, hξ]
      have hcost : stepsSpend ξ ≤ (ξ.length : ℚ) * BoundedSpend.c_max X := by
        induction ξ generalizing R
        case nil => simp [stepsSpend]
        case cons hd tl ih =>
          simp [stepsSpend]
          apply add_le_add (BoundedSpend.spend_le hd)
          apply ih
          simp [stepsObs] at hξ
          exact hξ.2
      exact_mod_cast hcost
    have h_ge : (step.costSpend : ℝ) ≤ delta (system X) R := by
      apply le_csSup h_bdd h_in_real
    exact lt_of_lt_of_le (show (0 : ℝ) < (step.costSpend : ℝ) by exact_mod_cast hpos) h_ge
  comp_reachable := fun {R1 R2 R3 Ra Rb} _ _ => ⟨Rb ++ Ra, rfl⟩ }

/-- The V1 trace model is segmentable. -/
def segmentable (X : Type) [DecidableEq X] : Segmentable (system X) where
  fiber_decomp := by
    intros R₁ R₂ R₂₁ ξ hc hξ
    simp [system, observableSystem] at hc
    cases hc
    dsimp only [Fiber, system, stepsObs] at hξ ⊢
    let n := R₂.length
    use ξ.take n, ξ.drop n
    constructor
    · simp [hiddenSystem]
    · constructor
      · dsimp only [Set.mem_setOf_eq] at hξ ⊢
        rw [List.map_take, hξ, List.take_append]
        simp [n]
      · dsimp only [Set.mem_setOf_eq] at hξ ⊢
        rw [List.map_drop, hξ, List.drop_append]
        simp [n]

end Coh.V1
