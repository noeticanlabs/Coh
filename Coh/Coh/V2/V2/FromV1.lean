import Coh.V2.Certified
import Coh.V2.BridgeLemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Basic

/-!
# V1 → V2 Bridge Layer

This module implements the canonical embedding of the V1 operational kernel
into the V2 projection-aware categorical completion. It defines a restricted
system of loops at a fixed witness vertex, providing a total monoidal structure
on the observable layer.
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
Restricted to loops at a witness to satisfy monoidal assumptions.
-/
def observableSystemFromV1 (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness))
    (h_comp : ∀ {t₁ t₂ t₁₂ : Trace X}, concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂) :
    ObservableSystem where
  V := { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness }
  comp t₂ t₁ :=
    let t₁₂ := concat t₁.1 t₂.1
    match h_c : t₁₂ with
    | none => none
    | some t_val =>
        if h_rv : RV t_val then
          some ⟨t_val, h_rv,
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
Total composition for restricted traces.
This allows providing a standard `Monoid` instance.
-/
def totalComp {X : Type} [DecidableEq X] {witness : X} {RV : Trace X → Prop}
    (h_comp : ∀ {t₁ t₂ t₁₂ : Trace X}, concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂)
    (t₂ t₁ : { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness }) :
    { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness } :=
  let t₁_val := t₁.1
  let t₂_val := t₂.1
  have h_dst_src : t₁_val.dst = t₂_val.src := t₁.2.2.2.trans t₂.2.2.1.symm
  let t₁₂_opt := concat t₁_val t₂_val
  match h_c : t₁₂_opt with
  | some t_val =>
    ⟨t_val, h_comp h_c t₁.2.1 t₂.2.1,
      by injection h_c with h_eq; rw [← h_eq]; exact t₁.2.2.1,
      by injection h_c with h_eq; rw [← h_eq]; exact t₂.2.2.2⟩
  | none => by unfold concat at h_c; split at h_c; contradiction

instance instMonoidRestrictedTrace (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness))
    (h_comp : ∀ {t₁ t₂ t₁₂ : Trace X}, concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂) :
    Monoid { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness } where
  mul := totalComp h_comp
  one := ⟨emptyTrace witness, h_id, rfl, rfl⟩
  mul_assoc t1 t2 t3 := by
    apply Subtype.ext
    simp [totalComp]
    match h12 : concat t1.1 t2.1, h23 : concat t2.1 t3.1 with
    | some t12, some t23 =>
      match h123 : concat t12 t3 with
      | some t123_val =>
        have h_assoc := concat_assoc t1.1 t2.1 t3.1 t12 t23 t123_val h12 h23 h123
        simp [h_assoc]
      | none =>
        -- This case is impossible due to dst=src
        have h_dst_src : t12.dst = t3.1.src := by
          injection h12 with h_eq
          rw [← h_eq]
          exact t2.2.2.2.trans t3.2.2.1.symm
        unfold concat at h123; split at h123; contradiction
    | _, _ =>
      -- These cases are also impossible
      repeat {
        unfold concat at *
        split at *
        contradiction
      }
  one_mul t := by
    apply Subtype.ext
    simp [totalComp, concat_id_left]
  mul_one t := by
    apply Subtype.ext
    simp [totalComp, concat_id_right]

/--
## Projection from hidden to observable

NOTE: Current projection is identity (singleton fiber model).
For a proper hidden/observable quotient, we would need to:
1. Define obs.G as a quotient by observable-equivalence relation
2. Or project to extract observable behavior from hidden traces

This is a fundamental architectural choice: identity gives Fib(R) = {R}
rather than a true fiber of hidden realizations over an observable trace.
-/
/--
## Projection from hidden to observable
-/
def projFromV1 (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness))
    (h_comp : ∀ {t₁ t₂ t₁₂ : Trace X}, concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂) :
    (hiddenSystemFromV1 X witness RV).G → (observableSystemFromV1 X witness RV h_id h_comp).V :=
  fun ξ => ξ

/--
## System instantiated from V1
-/
def systemFromV1 (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness))
    (h_comp : ∀ {t₁ t₂ t₁₂ : Trace X}, concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂) : System where
  Hid := hiddenSystemFromV1 X witness RV
  Obs := observableSystemFromV1 X witness RV h_id h_comp
  proj := projFromV1 X witness RV h_id h_comp

/--
## Assumptions from V1
-/
theorem assumptionsFromV1
    (X : Type) [DecidableEq X] (witness : X) (RV : Trace X → Prop)
    (hRV_id : ∀ (x : X), RV (emptyTrace x))
    (hRV_comp : ∀ (t₁ t₂ : Trace X) (t₁₂ : Trace X),
      concat t₁ t₂ = some t₁₂ →
      RV t₁ → RV t₂ → RV t₁₂) :
    Assumptions (systemFromV1 X witness RV (hRV_id witness) hRV_comp) := {
  obs_assoc := by
    intro R1 R2 R3 R12 R23 R123 h12 h23 h123a
    simp [systemFromV1, observableSystemFromV1] at *
    rw [← h12, ← h23, ← h123a]
    congr 1
    apply Subtype.ext
    simp [totalComp]
    match hr12 : concat R1.1 R2.1 with
    | some t12 =>
        match hr23 : concat R2.1 R3.1 with
        | some t23 =>
            match hr123 : concat t12 R3.1 with
            | some t123_val =>
                have h_assoc := concat_assoc R1.1 R2.1 R3.1 t12 t23 t123_val hr12 hr23 hr123
                simp [h_assoc]
            | none =>
                -- dst=src ensures this is some
                have h_dst_src : t12.dst = R3.1.src := by
                  injection hr12 with h_eq
                  rw [← h_eq]
                  exact R2.2.2.2.trans R3.2.2.1.symm
                unfold concat at hr123; split at hr123; contradiction
        | none =>
            -- dst=src ensures this is some
            have h_dst_src : R2.1.dst = R3.1.src := R2.2.2.2.trans R3.2.2.1.symm
            unfold concat at hr23; split at hr23; contradiction
    | none =>
        -- dst=src ensures this is some
        have h_dst_src : R1.1.dst = R2.1.src := R1.2.2.2.trans R2.2.2.1.symm
        unfold concat at hr12; split at hr12; contradiction

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
