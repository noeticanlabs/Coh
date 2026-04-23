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

/-! Hidden system with quotient -/
def hiddenSystemQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop) : HiddenSystem where
  G := { θ : HiddenRealization X // RV θ.trace ∧ θ.trace.src = witness ∧ θ.trace.dst = witness }
  comp θ₂ θ₁ :=
    match h_c : concat θ₂.1.trace θ₁.1.trace with
    | none => none
    | some t₁₂ =>
        if h_rv : RV t₁₂ then
          some ⟨⟨θ₂.1.wIdx + θ₁.1.wIdx, t₁₂⟩, h_rv, by simp, by simp⟩ else none
  cost θ := (traceDefect θ.1.trace : ℝ) + (θ.1.wIdx : ℝ)

/-! Observable system. -/
def observableSystemQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness)) : ObservableSystem where
  V := { t : Trace X // RV t ∧ t.src = witness ∧ t.dst = witness }
  comp t₂ t₁ :=
    match h_c : concat t₂.1 t₁.1 with
    | none => none
    | some t₁₂ =>
        if h_rv : RV t₁₂ then
          some ⟨t₁₂, h_rv, by simp, by simp⟩ else none
  id := ⟨emptyTrace witness, h_id, rfl, rfl⟩

/-! Projection: forget witness index - THIS IS THE KEY NON-DEGENERATE. -/
def projQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (θ : { θ : HiddenRealization X // RV θ.trace ∧ θ.trace.src = witness ∧ θ.trace.dst = witness }) :
    ObservableV1 X witness RV :=
  ⟨θ.1.trace, θ.2⟩

/-! Full system. -/
def systemFromV1Quotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness)) : System where
  Hid := hiddenSystemQuotient X witness RV
  Obs := observableSystemQuotient X witness RV h_id
  proj := projQuotient X witness RV

/-! Envelope: supremum over fiber costs. -/
def deltaQuotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness))
    (τ : ObservableV1 X witness RV) : ℝ :=
  sSup { c : ℝ | ∃ θ : (hiddenSystemQuotient X witness RV).G,
    projQuotient X witness RV θ = τ ∧
    (hiddenSystemQuotient X witness RV).cost θ = c }

end Coh.V2

/-! Assumptions instance for the quotient bridge. -/
def assumptionsFromV1Quotient (X : Type) [DecidableEq X]
    (witness : X) (RV : Trace X → Prop)
    (h_id : RV (emptyTrace witness)) :
    Assumptions (systemFromV1Quotient X witness RV h_id) :=
⟨
  /- obs_assoc -/ by
    intro R₁ R₂ R₃ R₁₂ R₂₃ R₁₂₃ h12 h23 h123
    -- Need to show: comp R₃ R₁₂ = R₁₂₃ ↔ comp R₂₃ R₁ = R₁₂₃
    unfold observableSystemQuotient.comp
    -- Since composition is none or some based on V1.concat
    -- This is equivalent to V1.concat_assoc
    cases h12; cases h23; cases h123
    <;> constructor
    <;> intro h
    <;> exact h,
  /- obs_id_right -/ by
    intro R
    have eq : R.1 = emptyTrace witness := R.2.2.2
    simp [observableSystemQuotient, comp, id, eq],
  /- obs_id_left -/ by
    intro R
    have eq : R.1 = emptyTrace witness := R.2.2.2
    simp [observableSystemQuotient, comp, id, eq],
  /- fiber_nonempty -/ by exact fun R => ⟨R, rfl⟩,
  /- fiber_bounded -/ by
    intro R
    use deltaQuotient X witness RV h_id R
    exact le_rfl,
  /- id_fiber_zero -/ by
    intro ξ hξ
    rw [mem_Fiber] at hξ
    simp [hiddenSystemQuotient, projQuotient] at hξ
    rw [hξ]
    simp [hiddenSystemQuotient, traceDefect_empty]
    have heq : (0 : ℝ) + ξ.1.wIdx = ξ.1.wIdx := by exact add_zero _
    rw [heq]
    exact natCast_injective,
  /- hidden_cost_add -/ by
    intro ξ₂ ξ₁ ξ hcomp
    simp [HiddenSystem.comp, hiddenSystemQuotient] at hcomp
    rcases hcomp with ⟨t₁₂, h_rv, heq⟩
    -- Hidden cost of composite is sum of costs
    have hadd := BridgeLemmas.traceDefect_concat ξ₂.1.trace ξ₁.1.trace t₁₂ heq
    simp [hiddenSystemQuotient] at hadd
    rw [hadd]
    ring,
  /- fiber_decomp -/ by
    intro R₁ R₂ R₂₁ hcomp ξ hξ
    -- Since we have proper composition, we can decompose
    use ξ, ξ
    constructor
    . simp [HiddenSystem.comp, hcomp]
    . exact hξ
⟩
