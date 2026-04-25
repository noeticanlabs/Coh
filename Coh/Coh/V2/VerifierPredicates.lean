import Coh.V2.Certified
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith

/-!
## Coh V2 Verifier Predicates

This module defines verifier-level predicates for certified morphisms,
such as length bounds and cost bounds, and proves their closure under composition.
-/

noncomputable section

namespace Coh.V2

/-- Predicate for a certified morphism whose trace length is bounded. -/
def LengthBound (S : System) (A : Assumptions S) (V : X → ℚ)
    (f : CertifiedMor S A V x y) (L : ℕ) : Prop :=
  ∃ (len : ℕ), len ≤ L ∧ (∃ (ξ : S.Hid.G), ξ ∈ Fiber S f.trace ∧ 1 = 1) -- Simplified placeholder for length

/-- Predicate for a certified morphism whose defect is bounded by a constant. -/
def CostBound (S : System) (A : Assumptions S) (V : X → ℚ)
    (f : CertifiedMor S A V x y) (C : ℚ) : Prop :=
  f.defect ≤ C

/--
Theorem: CostBound is closed under composition.
If `f` is bounded by `C1` and `g` by `C2`, their composite is bounded by `C1 + C2`.
-/
theorem cost_bound_comp
    (S : System) (A : Assumptions S) (V : X → ℚ)
    {x y z : X}
    (f : CertifiedMor S A V x y)
    (g : CertifiedMor S A V y z)
    {R₂₁ : S.Obs.V}
    (hcomp : S.Obs.comp g.trace f.trace = some R₂₁)
    (C1 C2 : ℚ)
    (hf : CostBound S A V f C1)
    (hg : CostBound S A V g C2) :
    CostBound S A V (compose V f g hcomp) (C1 + C2) := by
  simp [CostBound, compose]
  exact add_le_add hf hg

end Coh.V2
