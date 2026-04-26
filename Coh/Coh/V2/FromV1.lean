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
  proj_comp := fun {ξ₂ ξ₁ ξ} h => by
    dsimp only [hiddenSystem, observableSystem, stepsObs] at *
    cases h
    simp [List.map_append, List.append_assoc]

/-- Class for types with bounded spend per step. -/
class BoundedSpend (X : Type) where
  c_max : ℚ
  spend_le : ∀ s : Step X, s.costSpend ≤ c_max

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
  fiber_bounded := fun R => by
    use (R.length : ℚ) * BoundedSpend.c_max X
    intro q hq
    rcases hq with ⟨ξ, hξ, rfl⟩
    have hlen' := congrArg List.length (show stepsObs ξ = R from hξ)
    have hlen : ξ.length = R.length := by
      simpa [stepsObs, List.length_map] using hlen'
    have hcost := stepsSpend_bound (X := X) ξ
    simpa [system, hiddenSystem, hlen] using hcost
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
  structural_independence := by
    let x : X := Classical.choice (show Nonempty X from inferInstance)
    rcases HasPositiveSpend.positive_spend x with ⟨step, hsrc, hpos⟩
    let R : List X := [x]
    have h_in_real : (step.costSpend : ℝ) ∈ CostSetReal (system X) R := by
      refine ⟨step.costSpend, ?_, rfl⟩
      refine ⟨[step], ?_, by simp [system, hiddenSystem, stepsSpend]⟩
      change List.map Step.src [step] = R
      simp [R, hsrc]
    have h_bdd : BddAbove (CostSetReal (system X) R) := by
      use ((R.length : ℚ) * BoundedSpend.c_max X : ℝ)
      intro r hr
      rcases hr with ⟨q, hq, rfl⟩
      rcases hq with ⟨η, hη, rfl⟩
      have hlen' := congrArg List.length (show stepsObs η = R from hη)
      have hlen : η.length = R.length := by
        simpa [stepsObs, List.length_map] using hlen'
      have hcost := stepsSpend_bound (X := X) η
      exact_mod_cast (by simpa [hlen] using hcost)
    have hge : (step.costSpend : ℝ) ≤ delta (system X) R :=
      real_le_csSup h_bdd h_in_real
    refine ⟨R, lt_of_lt_of_le ?_ hge⟩
    exact_mod_cast hpos
  comp_reachable := fun {R₁ R₂ R₃ Ra Rb} _ _ => ⟨List.append Rb Ra, rfl⟩

/-- The V1 trace model is segmentable. -/
def segmentable (X : Type) [DecidableEq X] : Segmentable (system X) where
  fiber_decomp := by
    intros R₁ R₂ R₂₁ ξ hc hξ
    simp [system, observableSystem] at hc
    cases hc
    simp [Fiber, system, stepsObs] at hξ
    have hproj : stepsObs ξ = List.append R₂ R₁ := hξ
    let n := R₂.length
    use ξ.take n, ξ.drop n
    constructor
    · simp [system, hiddenSystem, List.take_append_drop]
    · constructor
      · show stepsObs (ξ.take n) = R₂
        have htake : List.take n (stepsObs ξ) = List.take n (List.append R₂ R₁) := by
          rw [hproj]
        rw [show stepsObs (ξ.take n) = List.take n (stepsObs ξ) by simp [stepsObs]]
        rw [htake]
        simp [n]
      · show stepsObs (ξ.drop n) = R₁
        have hdrop : List.drop n (stepsObs ξ) = List.drop n (List.append R₂ R₁) := by
          rw [hproj]
        rw [show stepsObs (ξ.drop n) = List.drop n (stepsObs ξ) by simp [stepsObs]]
        rw [hdrop]
        simp [n]

end Coh.V1
