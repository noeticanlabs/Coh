import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Basic

noncomputable section

namespace Coh.V1

inductive GlyphTag
| invoke
| bind
| route
| guard
| emit
deriving DecidableEq, Repr

structure ControlToken where
  opcode : String
  arg    : String
deriving DecidableEq, Repr

structure Glyph where
  tag         : GlyphTag
  surface     : String
  token       : ControlToken
  wf_surface  : Prop
  wf_token    : Prop

def Glyph.compiles (g : Glyph) : Prop :=
  g.wf_surface ∧ g.wf_token

structure Step (X : Type) where
  src         : X
  dst         : X
  glyph       : Glyph
  costSpend   : ℚ
  costDefect  : ℚ
  typed       : Prop
  compiles_ok : Glyph.compiles glyph

/-- Recursive predicate for a valid transition chain. -/
def is_chain {X : Type} : X → X → List (Step X) → Prop
| s, e, [] => s = e
| s, e, (step :: steps) => s = step.src ∧ is_chain step.dst e steps

structure Trace (X : Type) where
  src   : X
  dst   : X
  steps : List (Step X)
  chain : is_chain src dst steps

@[ext, simp]
theorem Trace.ext {X : Type} (t1 t2 : Trace X)
    (h_src : t1.src = t2.src) (h_dst : t1.dst = t2.dst) (h_steps : t1.steps = t2.steps) :
    t1 = t2 := by
  cases t1; cases t2
  subst h_src h_dst h_steps
  congr

/-- Helper: cost calculated directly from a list of steps. -/
def stepsSpend {X : Type} : List (Step X) → ℚ
| [] => 0
| s :: ss => s.costSpend + stepsSpend ss

def stepsDefect {X : Type} : List (Step X) → ℚ
| [] => 0
| s :: ss => s.costDefect + stepsDefect ss

theorem stepsSpend_append {X : Type} (as bs : List (Step X)) :
    stepsSpend (as ++ bs) = stepsSpend as + stepsSpend bs := by
  induction as
  case nil => simp [stepsSpend]
  case cons a as ih =>
    simp [stepsSpend, ih, add_assoc]

theorem stepsDefect_append {X : Type} (as bs : List (Step X)) :
    stepsDefect (as ++ bs) = stepsDefect as + stepsDefect bs := by
  induction as
  case nil => simp [stepsDefect]
  case cons a as ih =>
    simp [stepsDefect, ih, add_assoc]

def traceSpend {X : Type} : Trace X → ℚ
| ⟨_, _, [], _⟩ => 0
| ⟨_, dst, s :: ss, chain⟩ => 
    s.costSpend + traceSpend ⟨s.dst, dst, ss, by
      simp [is_chain] at chain
      exact chain.2
    ⟩
termination_by t => t.steps.length
decreasing_by
  simp [List.length_cons]
  apply Nat.lt_succ_self

/-- Link between traceSpend and stepsSpend. -/
theorem traceSpend_eq_stepsSpend {X : Type} (t : Trace X) :
    traceSpend t = stepsSpend t.steps := by
  match t with
  | ⟨src, dst, steps, chain⟩ =>
    induction steps generalizing src dst
    case nil => rfl
    case cons s ss ih =>
      simp [traceSpend, stepsSpend]
      apply ih s.dst dst (by
        simp [is_chain] at chain
        exact chain.2
      )

def traceDefect {X : Type} : Trace X → ℚ
| ⟨_, _, [], _⟩ => 0
| ⟨_, dst, s :: ss, chain⟩ => 
    s.costDefect + traceDefect ⟨s.dst, dst, ss, by
      simp [is_chain] at chain
      exact chain.2
    ⟩
termination_by t => t.steps.length
decreasing_by
  simp [List.length_cons]
  apply Nat.lt_succ_self

theorem traceDefect_eq_stepsDefect {X : Type} (t : Trace X) :
    traceDefect t = stepsDefect t.steps := by
  match t with
  | ⟨src, dst, steps, chain⟩ =>
    induction steps generalizing src dst
    case nil => rfl
    case cons s ss ih =>
      simp [traceDefect, stepsDefect]
      apply ih s.dst dst (by
        simp [is_chain] at chain
        exact chain.2
      )

def RVAccept (X : Type) (t : Trace X) : Prop := 
  ∀ s ∈ t.steps, s.typed

def emptyTrace {X : Type} (x : X) : Trace X :=
{ src   := x,
  dst   := x,
  steps := List.nil,
  chain := rfl }

/-- Lemma: is_chain is compositional under list concatenation. -/
theorem is_chain_concat {X : Type} (s m e : X) (t1 t2 : List (Step X)) :
    is_chain s m t1 → is_chain m e t2 → is_chain s e (t1 ++ t2) := by
  induction t1 generalizing s
  case nil =>
    intro h1 h2
    simp [is_chain] at h1
    rw [h1]
    exact h2
  case cons head tail ih =>
    intro h1 h2
    simp [is_chain] at h1
    simp [is_chain]
    exact ⟨h1.1, ih head.dst h1.2 h2⟩

def concat {X : Type} [DecidableEq X] (t₁ t₂ : Trace X) : Option (Trace X) :=
  if h : t₁.dst = t₂.src then
    some {
      src   := t₁.src,
      dst   := t₂.dst,
      steps := t₁.steps ++ t₂.steps,
      chain := is_chain_concat t₁.src t₁.dst t₂.dst t₁.steps t₂.steps t₁.chain (by rw [h]; exact t₂.chain)
    }
  else none

/-- Length of steps is additive under concatenation. -/
theorem trace_length_concat {X : Type} [DecidableEq X] {t₁ t₂ t₁₂ : Trace X}
    (h : concat t₁ t₂ = some t₁₂) :
    t₁₂.steps.length = t₁.steps.length + t₂.steps.length := by
  unfold concat at h
  split at h; case isFalse => contradiction
  case isTrue =>
    injection h with h_eq
    rw [← h_eq]
    simp [List.length_append]

theorem concat_assoc {X : Type} [DecidableEq X] (t₁ t₂ t₃ : Trace X) (t₁₂ t₂₃ t₁₂₃ : Trace X)
    (h12 : concat t₁ t₂ = some t₁₂)
    (h23 : concat t₂ t₃ = some t₂₃)
    (h123a : concat t₁₂ t₃ = some t₁₂₃) :
    concat t₁ t₂₃ = some t₁₂₃ := by
  unfold concat at h12 h23 h123a
  split at h12; case isFalse => contradiction
  case isTrue h12_dst =>
    injection h12 with h12_eq
    split at h23; case isFalse => contradiction
    case isTrue h23_dst =>
      injection h23 with h23_eq
      split at h123a; case isFalse => contradiction
      case isTrue h123_dst =>
        injection h123a with h123_eq
        unfold concat
        split; case isFalse h_neq =>
          have h23_src_val : t₂₃.src = t₂.src := by rw [← h23_eq]
          rw [h23_src_val, ← h12_dst] at h_neq
          contradiction
        case isTrue h_eq =>
          rw [← h123_eq]
          congr 1
          apply Trace.ext
          · have h_src_12 : t₁₂.src = t₁.src := by rw [← h12_eq]
            simp [h_src_12]
          · have h_dst_23 : t₂₃.dst = t₃.dst := by rw [← h23_eq]
            simp [h_dst_23]
          · have h_steps_12 : t₁₂.steps = t₁.steps ++ t₂.steps := by rw [← h12_eq]
            have h_steps_23 : t₂₃.steps = t₂.steps ++ t₃.steps := by rw [← h23_eq]
            simp [h_steps_12, h_steps_23, List.append_assoc]

theorem concat_id_right {X : Type} [DecidableEq X] (t : Trace X) :
    concat t (emptyTrace t.dst) = some t := by
  simp [concat, emptyTrace, Trace.ext]

theorem concat_id_left {X : Type} [DecidableEq X] (t : Trace X) :
    concat (emptyTrace t.src) t = some t := by
  simp [concat, emptyTrace, Trace.ext]

theorem concat_empty_left {X : Type} [DecidableEq X] {t₁ t₂ t₁₂ : Trace X}
    (h_id : t₁₂ = emptyTrace t₁.src) (h : concat t₁ t₂ = some t₁₂) :
    t₁.steps = [] ∧ t₂.steps = [] := by
  unfold concat at h; split at h; injection h with h_eq
  rw [h_id] at h_eq
  simp [emptyTrace] at h_eq
  exact h_eq.2

theorem concat_empty_right {X : Type} [DecidableEq X] {t₁ t₂ t₁₂ : Trace X}
    (h_id : t₁₂ = emptyTrace t₁.src) (h : concat t₁ t₂ = some t₁₂) :
    t₂.steps = [] := by
  unfold concat at h; split at h; injection h with h_eq
  rw [h_id] at h_eq
  simp [emptyTrace] at h_eq
  exact h_eq.2.2

theorem concat_id_id {X : Type} [DecidableEq X] {t₁ t₂ t₁₂ : Trace X}
    (h1 : t₁ = emptyTrace t₁.src) (h2 : t₂ = emptyTrace t₂.src) (h : concat t₁ t₂ = some t₁₂) :
    t₁₂ = emptyTrace t₁.src := by
  unfold concat at h; split at h; injection h with h_eq
  subst h1 h2
  simp [emptyTrace] at h_eq
  rw [← h_eq]
  apply Trace.ext <;> simp [emptyTrace]

theorem rv_id (X : Type) (x : X) : RVAccept X (emptyTrace x) := by
  simp [RVAccept, emptyTrace]

theorem rv_comp (X : Type) [DecidableEq X] (t₁ t₂ t₁₂ : Trace X)
    (h : concat t₁ t₂ = some t₁₂) :
    RVAccept X t₁ → RVAccept X t₂ → RVAccept X t₁₂ := by
  unfold concat at h
  split at h; case isFalse => contradiction
  case isTrue h_dst =>
    injection h with h_eq
    subst h_eq
    simp [RVAccept]
    intro h1 h2 s hs
    cases hs
    case inl h_in => exact h1 s h_in
    case inr h_in => exact h2 s h_in

structure CohMor (X : Type) (V : X → ℚ) (x y : X) where
  trace  : Trace X
  src_eq : trace.src = x
  dst_eq : trace.dst = y
  rv_ok  : RVAccept X trace
  valid  : V y + traceSpend trace ≤ V x + traceDefect trace

end Coh.V1
