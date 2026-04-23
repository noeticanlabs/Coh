import Coh.V1.Coh
import Mathlib.Data.Real.Basic

/-!
## Cost Type Bridge: ℚ → ℝ

V1 uses ℚ (rationals) for costs, V2 uses ℝ (reals).
This file provides explicit conversions and compatibility lemmas.
-/

namespace Coh.V1

/-- Convert rational to real (canonical embedding). -/
def ratToReal (q : ℚ) : ℝ := q

/-- Lift a rational-valued function to real-valued. -/
def liftToReal {X : Type} (f : X → ℚ) : X → ℝ :=
  fun x => ratToReal (f x)

/-- traceSpend compatibility. -/
theorem traceSpend_real {X : Type} (t : Trace X) :
    ratToReal (traceSpend t) = (traceSpend t : ℝ) :=
  rfl

/-- traceDefect compatibility. -/
theorem traceDefect_real {X : Type} (t : Trace X) :
    ratToReal (traceDefect t) = (traceDefect t : ℝ) :=
  rfl

/-- Cost additivity transfers to real. -/
theorem cost_additivity_real {X : Type} [DecidableEq X] {t₁ t₂ t₁₂ : Trace X} 
    (h : concat t₁ t₂ = some t₁₂) :
    (traceSpend t₁₂ : ℝ) = (traceSpend t₁ : ℝ) + (traceSpend t₂ : ℝ) :=
  by 
    rw [traceSpend_eq_stepsSpend, traceSpend_eq_stepsSpend t₁, traceSpend_eq_stepsSpend t₂]
    have h_steps : t₁₂.steps = t₁.steps ++ t₂.steps := by
      unfold concat at h; split at h; injection h with h_eq; rw [← h_eq]
    rw [h_steps, stepsSpend_append]
    simp

end Coh.V1
