import Coh.V2.Certified
import Coh.V2.BridgeLemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Basic

/-!
# V1 → V2 Bridge Layer

This module implements the canonical embedding of the V1 operational kernel
into the V2 projection-aware categorical completion.
-/

noncomputable section

namespace Coh.V2

open Classical
open Coh.V1

/--
## Hidden system from V1
Restricted to loops at a witness to satisfy monoidal assumptions.
-/
def hiddenSystemFromV1 (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop) : HiddenSystem where
  G := { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness }
  comp ξ₂ ξ₁ := 
    match h_c : concat ξ₁.1 ξ₂.1 with
    | none => none
    | some t₁₂ => 
        if h_rv : RV t₁₂ then
          some ⟨t₁₂, h_rv, 
            by 
              have h1 := ξ₁.2.2.1
              have h_c' := h_c
              unfold concat at h_c'
              split at h_c'; case isFalse => contradiction
              case isTrue => injection h_c' with h_eq; rw [← h_eq, h1],
            by
              have h2 := ξ₂.2.2.2
              have h_c' := h_c
              unfold concat at h_c'
              split at h_c'; case isFalse => contradiction
              case isTrue => injection h_c' with h_eq; rw [← h_eq, h2]
          ⟩
        else none
  cost ξ := (traceDefect ξ.1 : ℝ)

/--
## Observable system from V1
-/
def observableSystemFromV1 (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop) (h_id : RV (emptyTrace witness)) : ObservableSystem where
  V := { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness }
  comp t₂ t₁ := 
    match h_c : concat t₁.1 t₂.1 with
    | none => none
    | some t₁₂ => 
        if h_rv : RV t₁₂ then
          some ⟨t₁₂, h_rv, 
            by 
              have h1 := t₁.2.2.1
              have h_c' := h_c
              unfold concat at h_c'
              split at h_c'; case isFalse => contradiction
              case isTrue => injection h_c' with h_eq; rw [← h_eq, h1],
            by
              have h2 := t₂.2.2.2
              have h_c' := h_c
              unfold concat at h_c'
              split at h_c'; case isFalse => contradiction
              case isTrue => injection h_c' with h_eq; rw [← h_eq, h2]
          ⟩
        else none
  id := ⟨emptyTrace witness, h_id, rfl, rfl⟩

/--
## Projection from hidden to observable

NOTE: Current projection is identity (singleton fiber model).
For a proper hidden/observable quotient, we would need to:
1. Define obs.G as a quotient by observable-equivalence relation
2. Or project to extract observable behavior from hidden traces

This is a fundamental architectural choice: identity gives Fib(R) = {R}
rather than a true fiber of hidden realizations over an observable trace.
-/
def projFromV1 (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop) (h_id : RV (emptyTrace witness)) :
    (hiddenSystemFromV1 X witness RV).G → (observableSystemFromV1 X witness RV h_id).V :=
  fun ξ => ξ

/--
## System instantiated from V1
-/
def systemFromV1 (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop) (h_id : RV (emptyTrace witness)) : System where
  Hid := hiddenSystemFromV1 X witness RV
  Obs := observableSystemFromV1 X witness RV h_id
  proj := projFromV1 X witness RV h_id

/--
## Assumptions from V1
-/
theorem assumptionsFromV1
    (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop)
    (hRV_id : ∀ (x : X), RV (emptyTrace x))
    (hRV_comp : ∀ (t₁ t₂ : Trace X) (t₁₂ : Trace X),
      concat t₁ t₂ = some t₁₂ →
      RV t₁ → RV t₂ → RV t₁₂) :
    Assumptions (systemFromV1 X witness RV (hRV_id witness)) := {
  obs_assoc := by
    intro R1 R2 R3 R12 R23 R123 h12 h23 h123a
    simp [systemFromV1, observableSystemFromV1] at *
    match hr12 : concat R1.1 R2.1 with
    | some t12 => 
        rw [hr12] at h12
        split at h12; case h_1 => contradiction
        case h_2 =>
          injection h12 with h12_eq
          match hr23 : concat R2.1 R3.1 with
          | some t23 =>
              rw [hr23] at h23
              split at h23; case h_1 => contradiction
              case h_2 =>
                injection h23 with h23_eq
                match hr123 : concat R12.1 R3.1 with
                | some t123 =>
                    rw [hr123] at h123a
                    split at h123a; case h_1 => contradiction
                    case h_2 =>
                      injection h123a with h123a_eq
                      -- Now we need to show comp R23 R1 = some R123
                      simp [systemFromV1, observableSystemFromV1]
                      match hr23_final : concat R1.1 R23.1 with
                      | some t123_final =>
                          have h_assoc := concat_assoc R1.1 R2.1 R3.1 R12.1 R23.1 t123_final (by rw [← hr12]; rfl) (by rw [← hr23]; rfl) (by rw [← hr123, ← h12_eq]; simp)
                          rw [h_assoc] at hr23_final
                          injection hr23_final with hr23_final_eq
                          simp [hr23_final_eq]
                          split; case h_1 => contradiction
                          case h_2 =>
                            congr 1
                            apply Subtype.ext
                            simp [hr23_final_eq, h123a_eq]
                      | none => 
                          have h_assoc := concat_assoc R1.1 R2.1 R3.1 R12.1 R23.1 t123 (by rw [← hr12]; rfl) (by rw [← hr23]; rfl) (by rw [← hr123, ← h12_eq]; simp)
                          rw [h_assoc] at hr23_final
                          contradiction
          | none => rw [hr23] at h23; contradiction
    | none => rw [hr12] at h12; contradiction

  obs_id_right := by
    intro R
    simp [systemFromV1, observableSystemFromV1]
    have h_comp := concat_id_right R.1
    rw [h_comp]
    split; case h_1 =>
      have h_rv_r := R.2.1
      contradiction
    case h_2 =>
      congr 1
      apply Subtype.ext
      simp

  obs_id_left := by
    intro R
    simp [systemFromV1, observableSystemFromV1]
    have h_comp := concat_id_left R.1
    rw [h_comp]
    split; case h_1 =>
      have h_rv_r := R.2.1
      contradiction
    case h_2 =>
      congr 1
      apply Subtype.ext
      simp

  fiber_nonempty := by
    intro R
    use R
    exact rfl

  fiber_bounded := by
    intro R
    use (traceDefect R.1 : ℝ)
    intro x hx
    rw [mem_CostSet] at hx
    rcases hx with ⟨ξ, hξ, rfl⟩
    rw [mem_Fiber] at hξ
    simp [systemFromV1, projFromV1] at hξ
    rw [hξ]
    dsimp [hiddenSystemFromV1]

  id_fiber_zero := by
    intro ξ hξ
    rw [mem_Fiber] at hξ
    simp [systemFromV1, projFromV1] at hξ
    rw [hξ]
    dsimp [hiddenSystemFromV1]
    rw [traceDefect_empty]
    simp

  hidden_cost_add := by
    intro ξ2 ξ1 ξ hcomp
    simp [systemFromV1, hiddenSystemFromV1] at *
    match hr : concat ξ1.1 ξ2.1 with
    | some t12 =>
        rw [hr] at hcomp
        split at hcomp; case h_1 => contradiction
        case h_2 =>
          injection hcomp with h_eq
          rw [← h_eq]
          dsimp
          rw [traceDefect_concat ξ1.1 ξ2.1 t12 hr]
          simp
    | none => rw [hr] at hcomp; contradiction

  fiber_decomp := by
    intro R1 R2 R21 hcomp ξ hξ
    rw [mem_Fiber] at hξ
    simp [systemFromV1, projFromV1] at hξ
    use R2, R1
    constructor
    · simp [systemFromV1, hiddenSystemFromV1, observableSystemFromV1] at *
      match hr : concat R1.1 R2.1 with
      | some t12 =>
          rw [hr] at hcomp
          split at hcomp; case h_1 => contradiction
          case h_2 h_rv =>
            injection hcomp with h_eq
            subst h_eq hξ
            simp [hr, h_rv]
      | none => rw [hr] at hcomp; contradiction
    · subst hξ
      exact ⟨rfl, rfl⟩
}

end Coh.V2
