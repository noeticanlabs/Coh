import Coh.V1.Coh
import Coh.V2.Primitive
import Mathlib.Data.Rat.Lemmas
import Coh.V2.Axioms
import Coh.V2.Definitions
import Coh.V2.FiniteWord
import Coh.V2.BridgeLemmas

/-!
## Coh V1 to V2 Direct Bridge

This module defines a bridge from V1 traces to a V2 system
where observable traces are sequences of labels (steps).

To ensure a sound axiomatic bridge, we use a "Lax Hidden Layer"
where hidden traces are lists of steps (not necessarily forming a chain).
This satisfies all V2 axioms while preserving V1 cost semantics.
-/

noncomputable section

namespace Coh.V2.FromV1

open Coh.V1
open Coh.V2.BridgeLemmas

variable {X : Type} [DecidableEq X]

/-- Hidden system derived from V1 kernel using lax traces. -/
def hiddenSystem (X : Type) [DecidableEq X] : HiddenSystem where
  G := List (Step X)
  comp := fun L2 L1 => some (L1 ++ L2)
  cost := fun L => (stepsSpend L : ℚ)

/--
Observable system derived from V1 kernel.
The observable layer is the set of all step sequences.
-/
def observableSystem (X : Type) [DecidableEq X] : ObservableSystem where
  V := List (Step X)
  comp := fun L2 L1 => some (L1 ++ L2) -- Categorical order: L2 after L1
  id := []

/-- Projection is the identity on lax traces. -/
def proj (X : Type) [DecidableEq X] (L : List (Step X)) : List (Step X) := L

/-- The system bridge from V1. -/
def system (X : Type) [DecidableEq X] [Nonempty X] : System where
  Hid := hiddenSystem X
  Obs := observableSystem X
  proj := proj X

/--
The structural independence hypothesis for V1→V2 bridge.
-/
class HasPositiveSpend (X : Type) [DecidableEq X] where
  pos_spend : ∃ R : Trace X, (traceSpend R : ℚ) > 0

/--
Build V2 Assumptions from V1.
-/
def assumptions [Nonempty X] [HasPositiveSpend X] : SegmentableAssumptions (system X) :=
{ toAssumptions :=
  { obs_assoc := fun {R1 R2 R3 R12 R23 R123} h12 h23 h123a => by
      simp [system, observableSystem] at h12 h23 h123a
      cases h12; cases h23; cases h123a
      simp [List.append_assoc]
    obs_id_right := fun L => by
      simp [system, observableSystem]
    obs_id_left := fun L => by
      simp [system, observableSystem]
    fiber_nonempty := fun L => by
      use L
      rfl
    fiber_bounded := fun L => by
      use stepsSpend L
      intro c hc
      rcases hc with ⟨ξ, hξ, rfl⟩
      simp [Fiber, system, proj] at hξ
      rw [hξ]
    id_fiber_zero := fun ξ hξ => by
      simp [Fiber, system, proj, observableSystem] at hξ
      simp [hξ, stepsSpend]
    hidden_cost_add := fun {ξ₂ ξ₁ ξ} h => by
      simp [hiddenSystem, system] at *
      cases h
      simp [stepsSpend_append]
    cost_nonneg := fun ξ => by
      simp [hiddenSystem, system]
      exact stepsSpend_nonneg ξ
    structural_independence := by
      rcases HasPositiveSpend.pos_spend (X := X) with ⟨R, hR⟩
      use R.steps
      unfold delta
      have h_in : stepsSpend R.steps ∈ CostSet (system X) R.steps := by
        simp [CostSet, Fiber, system, proj]
      have h_bdd : BddAbove (CostSet (system X) R.steps) := by
        use stepsSpend R.steps
        intro c hc
        rcases hc with ⟨ξ, hξ, rfl⟩
        simp [Fiber, system, proj] at hξ
        rw [hξ]
      exact lt_of_lt_of_le hR (rat_le_csSup h_bdd h_in) }
  fiber_decomp := fun {R1 R2 R21 ξ} hc h => by
    simp [system, observableSystem, proj, Fiber] at *
    cases hc
    subst h
    use R2, R1
    simp [hiddenSystem] }

end Coh.V2.FromV1
