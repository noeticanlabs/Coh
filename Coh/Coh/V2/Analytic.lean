import Coh.V2.Axioms
import Mathlib.Data.Rat.Lemmas

/-!
## Coh V2 Rational Properties

This module provides utility lemmas for the rational defect envelope [`delta`](Coh/Coh/V2/Definitions.lean).
In the strict rational rework, these are largely direct consequences of the system axioms.
-/

namespace Coh.V2

/--
The delta function is zero at the identity (Axiomatic).
-/
theorem delta_id_thm {S : System} (A : Assumptions S) : delta S S.Obs.id = 0 :=
  A.delta_id

/--
The delta function is non-negative (Axiomatic).
-/
theorem delta_nonneg_thm {S : System} (A : Assumptions S) (R : S.Obs.V) :
    0 ≤ delta S R :=
  A.delta_nonneg R

/--
The delta function is bounded by any upper bound on the fiber cost set (By delta_le).
-/
theorem delta_le_of_bounded_thm {S : System} {R : S.Obs.V} (A : Assumptions S)
    {B : ℚ} (hB : S.delta R ≤ B) : delta S R ≤ B :=
  hB

/--
The delta function is subadditive under observable composition (Axiomatic).
-/
theorem delta_subadd_thm {S : System} (A : Assumptions S)
    {R₁ R₂ R₂₁ : S.Obs.V} (hc : S.Obs.comp R₂ R₁ = some R₂₁) :
    delta S R₂₁ ≤ delta S R₂ + delta S R₁ :=
  A.delta_subadd hc

end Coh.V2
