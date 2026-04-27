import Coh.V1.Coh
import Coh.V2.Primitive
import Coh.V2.Definitions
import Coh.V2.Axioms
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith

/-!
## Coh V1 to V2 Bridge (Rational Version)

This module defines the mapping from the V1 Operational Trace model
to the V2 Categorical system using strictly rational types.
-/

namespace Coh.V1

open Coh.V2

/-- Observable projection: maps a sequence of steps to their source states. -/
def stepsObs {X : Type} (ss : List (Step X)) : List X :=
  ss.map Step.src

/-- Class for types with bounded spend per step. -/
class BoundedSpend (X : Type) where
  c_max : ℚ
  c_max_nonneg : 0 ≤ c_max
  c_max_pos : 0 < c_max
  spend_le : ∀ s : Step X, s.costSpend ≤ c_max


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
  complexity := fun L => (L.length : ℚ)

/-- The V1 to V2 system mapping. -/
def system (X : Type) [DecidableEq X] [BoundedSpend X] : System where
  Hid := hiddenSystem X
  Obs := observableSystem X
  proj := stepsObs
  proj_comp := fun {ξ₂ ξ₁ ξ} h => by
    dsimp only [hiddenSystem, observableSystem, stepsObs] at *
    cases h
    simp [List.map_append]
  delta := fun R => (R.length : ℚ) * BoundedSpend.c_max X

/-- Positive spend assumption for V1 states. -/
class HasPositiveSpend (X : Type) where
  positive_spend : ∀ x : X, ∃ step : Step X, step.src = x ∧ step.costSpend > 0

private def bridgeGlyph : Glyph :=
  { tag := GlyphTag.invoke
    surface := ""
    token := { opcode := "", arg := "" }
    wf_surface := True
    wf_token := True }

private def zeroStep {X : Type} (x : X) : Step X :=
  { src := x
    dst := x
    glyph := bridgeGlyph
    costSpend := 0
    costDefect := 0
    spend_nonneg := by norm_num
    defect_nonneg := by norm_num
    typed := True
    compiles_ok := by
      simp [bridgeGlyph, Glyph.compiles] }

private theorem stepsSpend_bound {X : Type} [BoundedSpend X] (ξ : List (Step X)) :
    stepsSpend ξ ≤ (ξ.length : ℚ) * BoundedSpend.c_max X := by
  induction ξ with
  | nil => simp [stepsSpend]
  | cons hd tl ih =>
      have hmax : hd.costSpend ≤ BoundedSpend.c_max X := BoundedSpend.spend_le hd
      have hsum : hd.costSpend + stepsSpend tl ≤
          BoundedSpend.c_max X + (tl.length : ℚ) * BoundedSpend.c_max X :=
        add_le_add hmax ih
      simpa [stepsSpend, List.length, add_mul, add_comm, add_left_comm, add_assoc] using hsum

/-- Verification of Assumptions for the V1->V2 bridge. -/
def assumptions (X : Type) [DecidableEq X] [Nonempty X] [BoundedSpend X] [HasPositiveSpend X] : Assumptions (system X) where
  obs_assoc := fun {R₁ R₂ R₃ R₁₂ R₂₃ R₁₂₃} h12 h23 h123 => by
    dsimp only [system, observableSystem] at *
    cases h12; cases h23; cases h123
    rw [List.append_assoc]
  obs_id_right := fun R => by dsimp only [system, observableSystem]; rw [List.append_nil]
  obs_id_left := fun R => by dsimp only [system, observableSystem]; rw [List.nil_append]
  fiber_nonempty := fun R => by
    refine ⟨R.map zeroStep, ?_⟩
    change List.map Step.src (List.map zeroStep R) = R
    induction R with
    | nil => rfl
    | cons hd tl ih => simp [zeroStep, ih]
  delta_le := fun {R} {ξ} hξ => by
    simp [Fiber, stepsObs] at hξ
    have hlen' := congrArg List.length (show stepsObs ξ = R from hξ)
    have hlen : ξ.length = R.length := by
      simpa [stepsObs, List.length_map] using hlen'
    have hcost := stepsSpend_bound (X := X) ξ
    dsimp [system]
    rw [← hlen]
    exact hcost
  delta_id := by simp [system]
  id_fiber_zero := fun ξ hξ => by
    have hproj : stepsObs ξ = [] := hξ
    have hlen : ξ.length = 0 := by
      simpa [stepsObs, List.length_map] using congrArg List.length hproj
    cases ξ with
    | nil => rfl
    | cons hd tl => cases hlen
  hidden_cost_add := fun {ξ₂ ξ₁ ξ} h => by
    simp [system, hiddenSystem] at h
    cases h
    simp [system, hiddenSystem, stepsSpend_append]
  cost_nonneg := fun ξ => stepsSpend_nonneg ξ
  delta_nonneg := fun R => by
    simp [system]
    apply mul_nonneg
    · simp
    · exact BoundedSpend.c_max_nonneg

  delta_subadd := fun {R₁ R₂ R₂₁} hc => by
    simp [system, observableSystem] at hc
    cases hc
    simp [system]
    rw [List.length_append, Nat.cast_add, add_mul]
  structural_independence := by
    -- We use a singleton observable [x] as the witness.
    -- Since c_max > 0, delta [x] = 1 * c_max > 0.
    rcases (inferInstance : Nonempty X) with ⟨x⟩
    use [x]
    simp [system]
    exact BoundedSpend.c_max_pos

  comp_reachable := fun {R₁ R₂ R₃ Ra Rb} _ _ => ⟨List.append Rb Ra, rfl⟩

end Coh.V1
