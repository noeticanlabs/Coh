import Coh.V2.Certified
import Coh.V2.BridgeLemmas
import Coh.V1.Coh
import Mathlib.Data.Real.Basic

/-!
# V1 → V2 Quotient Bridge (Proper Hidden/Observable)

This module implements a proper hidden/observable quotient construction:
- HiddenRealization: V1 trace + witness index (internal state)
- Observable: V1 traces at a fixed witness
- projQuotient: forgets witness index → proper projection
- Fiber: multiple realizations mapping to same observable
- delta: supremum over hidden costs in fiber

Unlike FromV1 (degenerate identity projection),
this gives genuine fiber geometry.
-/

noncomputable section

namespace Coh.V2

open Classical
open Coh.V1

/-- Hidden realization: trace + witness index. -/
structure HiddenRealization (X : Type) [DecidableEq X] where
  wIdx : ℕ
  trace : Trace X

/-- Observable type: restricted traces. -/
def ObservableV1 (X : Type) [DecidableEq X] (witness : X)
    (RV : Trace X → Prop) : Type :=
  { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness }

/-- Hidden system: refined traces with a witness index. -/
def hiddenSystemQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop) : HiddenSystem where
  G := { θ : HiddenRealization X // RV θ.trace ∧ θ.trace.src = witness ∧ θ.trace.dst = witness }
  comp θ₂ θ₁ :=
    match h_c : concat θ₁.val.trace θ₂.val.trace with
    | none => none
    | some t₁₂ =>
        if h_rv : RV t₁₂ then
          some ⟨⟨θ₁.val.wIdx + θ₂.val.wIdx, t₁₂⟩, h_rv,
            by
              unfold concat at h_c
              split at h_c; case isFalse => contradiction
              case isTrue h_eq =>
                injection h_c with h_val
                simp [h_val, θ₁.2.2.1],
            by
              unfold concat at h_c
              split at h_c; case isFalse => contradiction
              case isTrue h_eq =>
                injection h_c with h_val
                simp [h_val, θ₂.2.2.2]
          ⟩ else none
  cost θ :=
    if θ.val.trace = emptyTrace witness then 0
    else (traceDefect θ.val.trace : ℝ) + (θ.val.wIdx : ℝ)

/-- Equivalence relation: hidden realizations are equivalent if their traces match. -/
def Rel (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop)
    (θ₁ θ₂ : { θ : HiddenRealization X // RV θ.trace ∧ θ.trace.src = witness ∧ θ.trace.dst = witness }) : Prop :=
  θ₁.1.trace = θ₂.1.trace

instance (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop) :
    Setoid { θ : HiddenRealization X // RV θ.trace ∧ θ.trace.src = witness ∧ θ.trace.dst = witness } where
  r := Rel X witness RV
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

/-- Observable system obtained as a quotient of the hidden system. -/
def observableSystemQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness)) : ObservableSystem where
  V := Quotient (instSetoid X witness RV)
  comp v₂ v₁ :=
    v₁.liftOn₂ v₂ (fun θ₁ θ₂ =>
      match h_c : concat θ₁.val.trace θ₂.val.trace with
      | none => none
      | some t₁₂ =>
          if h_rv : RV t₁₂ then
            some (Quotient.mk' ⟨⟨0, t₁₂⟩, h_rv,
              by unfold concat at h_c; split at h_c; injection h_c with h_val; rw [← h_val]; exact θ₁.2.2.1,
              by unfold concat at h_c; split at h_c; injection h_c with h_val; rw [← h_val]; exact θ₂.2.2.2⟩)
          else none)
      (by
        intro a1 a2 b1 b2 h1 h2
        simp [Rel] at h1 h2
        simp [h1, h2])
  id := Quotient.mk' ⟨⟨0, emptyTrace witness⟩, h_id, rfl, rfl⟩

/-- Projection from hidden to observable by mapping to the quotient class. -/
def projQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop) :
    (hiddenSystemQuotient X witness RV).G → (observableSystemQuotient X witness RV (Classical.choice inferInstance)).V :=
  fun θ => Quotient.mk' θ

/-! Full system. -/
def systemFromV1Quotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness)) : System where
  Hid := hiddenSystemQuotient X witness RV
  Obs := observableSystemQuotient X witness RV h_id
  proj := projQuotient X witness RV

/-- Envelope: supremum over fiber costs. -/
def deltaQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness))
    (τ : (observableSystemQuotient X witness RV h_id).V) : ℝ :=
  sSup { c : ℝ | ∃ θ : (hiddenSystemQuotient X witness RV).G,
    Quotient.mk' θ = τ ∧
    (hiddenSystemQuotient X witness RV).cost θ = c }

end Coh.V2

/-! Assumptions instance for the quotient bridge. -/
theorem assumptionsFromV1Quotient (X : Type) [DecidableEq X]
    (witness : X) (RV : → Prop)
    (h_id : RV (emptyTrace witness))
    (h_bdd : ∀ τ, BddAbove { c : ℝ | ∃ θ : (hiddenSystemQuotient X witness RV).G, Quotient.mk' θ = τ ∧ (hiddenSystemQuotient X witness RV).cost θ = c }) :
    Assumptions (systemFromV1Quotient X witness RV h_id) :=
{
  obs_assoc := by
    intro R₁ R₂ R₃ R₁₂ R₂₃ R₁₂₃ h12 h23 h123a
    simp [observableSystemQuotient] at *
    rw [← h12, ← h23, ← h123a]
    congr
  obs_id_right := by
    intro R
    simp [observableSystemQuotient, systemFromV1Quotient]
    apply Quotient.inductionOn R
    intro θ
    simp
    congr 1
    apply Subtype.ext
    simp [HiddenRealization, concat_id_right]
  obs_id_left := by
    intro R
    simp [observableSystemQuotient, systemFromV1Quotient]
    apply Quotient.inductionOn R
    intro θ
    simp
    congr 1
    apply Subtype.ext
    simp [HiddenRealization, concat_id_left]
  fiber_nonempty := by
    intro R
    apply Quotient.inductionOn R
    intro θ
    use θ
    simp [projQuotient]
  fiber_bounded := by
    intro R
    exact h_bdd R
  id_fiber_zero := by
    intro ξ hξ
    simp [projQuotient, mem_Fiber] at hξ
    simp [hiddenSystemQuotient, hξ]
  hidden_cost_add := by
    intro ξ₂ ξ₁ ξ hcomp
    simp [hiddenSystemQuotient] at *
    match hr : concat ξ₁.1.trace ξ₂.1.trace with
    | some t₁₂ =>
      rw [hr] at hcomp
      split at hcomp; case isFalse => contradiction
      case isTrue h_rv =>
        injection hcomp with h_eq
        rw [← h_eq]
        simp
        split_ifs with h_id
        · -- Case: composite is emptyTrace. Then both components must be emptyTrace.
          have h_steps := concat_empty_left h_id hr
          have h1 : ξ₁.1.trace = emptyTrace witness := Trace.ext _ _ rfl rfl h_steps.1
          have h2 : ξ₂.1.trace = emptyTrace witness := Trace.ext _ _ rfl rfl h_steps.2
          simp [h1, h2]
        · -- Case: composite is not emptyTrace.
          rw [traceDefect_concat _ _ _ hr]
          -- We still have the issue if one component is emptyTrace.
          split_ifs with h1 h2
          · -- Both empty. Then composite is empty, contradiction.
            have h1_eq : ξ₁.1.trace = emptyTrace witness := Trace.ext _ _ rfl rfl h1
            have h2_eq : ξ₂.1.trace = emptyTrace witness := Trace.ext _ _ rfl rfl h2
            have h_comp_id := concat_id_id h1_eq h2_eq hr
            contradiction
          · -- ξ1 empty, ξ2 not.
            simp [traceDefect_empty, h1]
          · -- ξ2 empty, ξ1 not.
            simp [traceDefect_empty, h2]
          · -- Both non-empty.
            ring
    | none => rw [hr] at hcomp; contradiction
  fiber_decomp := by
    intro R₁ R₂ R₂₁ hcomp ξ hξ
    simp [projQuotient, mem_Fiber] at hξ
    -- R1, R2 are classes. Let's pick representatives.
    apply Quotient.inductionOn₂ R₁ R₂
    intro θ1 θ2 hc
    simp [observableSystemQuotient] at hc
    match hr : concat θ1.1.trace θ2.1.trace with
    | some t12 =>
        rw [hr] at hc
        split at hc; case isFalse => contradiction
        case isTrue h_rv =>
          injection hc with h_eq
          -- Now θ1.trace ++ θ2.trace = ξ.trace (up to the quotient's lift)
          -- Actually we can just use ξ.wIdx and split it.
          use ⟨⟨0, θ2.1.trace⟩, θ2.2⟩, ⟨⟨ξ.1.wIdx, θ1.1.trace⟩, θ1.2⟩
          constructor
          · simp [hiddenSystemQuotient, h_rv]
            rw [hr]
            apply Subtype.ext; simp
            rw [h_eq, ← hξ]
          · constructor
            · rw [h_eq]
              simp [Rel]
            · simp [Rel]
}
