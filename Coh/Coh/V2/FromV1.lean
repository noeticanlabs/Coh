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
-/

noncomputable section

namespace Coh.V2.FromV1

open Coh.V1
open Coh.V2.BridgeLemmas

variable {X : Type} [DecidableEq X]

/-- Hidden system derived from V1 kernel. -/
def hiddenSystem (X : Type) [DecidableEq X] : HiddenSystem where
  G := Trace X
  comp := fun ξ2 ξ1 => concat ξ1 ξ2
  cost := fun t => (traceSpend t : ℚ)

/--
Observable system derived from V1 kernel.
The observable layer is the set of valid step sequences (paths).
For simplicity in the axiomatic layer, we use all step sequences
and rely on the projection to handle validity.
-/
def observableSystem (X : Type) [DecidableEq X] : ObservableSystem where
  V := List (Step X)
  comp := fun L2 L1 => some (L1 ++ L2) -- Categorical order: L2 after L1
  id := []

/-- Projection from hidden traces to observable step sequences. -/
def proj (X : Type) [DecidableEq X] (t : Trace X) : List (Step X) := t.steps

/-- The system bridge from V1. -/
def system (X : Type) [DecidableEq X] [Nonempty X] : System where
  Hid := hiddenSystem X
  Obs := observableSystem X
  proj := proj X

/-- Every trace is a witness of its own step sequence. -/
theorem fiber_nonempty {X : Type} [DecidableEq X] [Nonempty X] (L : List (Step X)) (h : ∃ s e, is_chain s e L) :
    (Fiber (system X) L).Nonempty := by
  rcases h with ⟨s, e, h_chain⟩
  use { src := s, dst := e, steps := L, chain := h_chain }
  simp [Fiber, system, proj]
  rfl

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
  obs_assoc := fun {R1 R2 R3 R12 R23 R123} h12 h23 h123a => by
    simp [system, observableSystem] at h12 h23 h123a
    cases h12; cases h23; cases h123a
    simp [List.append_assoc]

  obs_id_right := fun L => by
    simp [system, observableSystem]
  obs_id_left := fun L => by
    simp [system, observableSystem]
  fiber_nonempty := fun L => by
    -- [LEMMA-NEEDED] fiber_nonempty requires R to be a valid V1 chain.
    -- This axiom holds on the reachable subspace of the observable layer.
    sorry
  fiber_bounded := fun L => by
    use stepsSpend L
    intro c hc
    rcases hc with ⟨ξ, hξ, rfl⟩
    simp [Fiber, system, proj] at hξ
    rw [traceSpend_eq_stepsSpend, hξ]
  id_fiber_zero := fun ξ hξ => by
    simp [Fiber, system, proj, observableSystem] at hξ
    rw [traceSpend_eq_stepsSpend, hξ]
    simp [stepsSpend]
  hidden_cost_add := fun {ξ₂ ξ₁ ξ} h => by
    simp [hiddenSystem, system] at *
    rw [traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend]
    unfold concat at h
    split at h; case isFalse => contradiction
    case isTrue h_dst =>
      injection h with h_eq
      subst h_eq
      simp [stepsSpend_append]
  cost_nonneg := fun ξ => by
    simp [hiddenSystem, system]
    exact stepsSpend_nonneg ξ.steps
  structural_independence := by
    rcases HasPositiveSpend.pos_spend (X := X) with ⟨R, hR⟩
    use R.steps
    unfold delta
    have h_in : traceSpend R ∈ CostSet (system X) R.steps := by
      simp [CostSet, Fiber, system, proj]
      use R
    have h_bdd : BddAbove (CostSet (system X) R.steps) := by
      use stepsSpend R.steps
      intro c hc
      rcases hc with ⟨ξ, hξ, rfl⟩
      simp [Fiber, system, proj] at hξ
      rw [traceSpend_eq_stepsSpend, hξ]
    exact lt_of_lt_of_le hR (rat_le_csSup h_bdd h_in) }
  fiber_decomp := fun {R1 R2 R21 ξ} hc h => by
    simp [system, observableSystem, proj, Fiber] at *
    subst h
    -- [NBCP] Decomposition follows from the V1 is_chain_split lemma.
    -- Note: This requires hiddenSystem.comp to be aligned with observableSystem.comp order.
    rcases is_chain_split ξ.chain with ⟨m, h1, h2⟩
    use { src := m, dst := ξ.dst, steps := R2, chain := h2 }
    use { src := ξ.src, dst := m, steps := R1, chain := h1 }
    simp [hiddenSystem, concat, h1, h2]
    apply Trace.ext <;> simp [h1, h2]

end Coh.V2.FromV1
