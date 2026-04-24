import Coh.V2.Definitions
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
## Coh V2 Axiomatic Framework

This module formalizes the core axioms of the Coh V2 framework.
The `Assumptions` structure captures the requirements for a `System` to be
well-behaved, mirroring the analytical conditions defined in the manuscript.
-/

namespace Coh.V2

universe u

/--
Frozen Coh V2 assumptions.

These are the specification-level assumptions mirrored from the manuscript:
observable associativity and identity, fiber nonemptiness and boundedness,
identity fiber zero-cost, exact hidden additivity, and composite-fiber
decomposition.
-/
structure Assumptions (S : System) : Prop where
  /-- Observable associativity in witness-threaded form. -/
  obs_assoc :
    ∀ {R₁ R₂ R₃ R₁₂ R₂₃ R₁₂₃ : S.Obs.V},
      S.Obs.comp R₂ R₁ = some R₁₂ →
      S.Obs.comp R₃ R₂ = some R₂₃ →
      S.Obs.comp R₃ R₁₂ = some R₁₂₃ →
      S.Obs.comp R₂₃ R₁ = some R₁₂₃

  /-- Right identity relative to the `comp R₂ R₁` convention. -/
  obs_id_right :
    ∀ (R : S.Obs.V), S.Obs.comp R S.Obs.id = some R

  /-- Left identity relative to the `comp R₂ R₁` convention. -/
  obs_id_left :
    ∀ (R : S.Obs.V), S.Obs.comp S.Obs.id R = some R

  /-- Every observable trace has at least one hidden witness. -/
  fiber_nonempty :
    ∀ (R : S.Obs.V), (Fiber S R).Nonempty

  /-- Every fiber cost set is bounded above. -/
  fiber_bounded :
    ∀ (R : S.Obs.V), BddAbove (CostSet S R)

  /-- Every hidden witness in the identity fiber has zero cost. -/
  id_fiber_zero :
    ∀ ξ ∈ Fiber S S.Obs.id, S.Hid.cost ξ = 0

  /-- Hidden cost is exactly additive on defined hidden composition. -/
  hidden_cost_add :
    ∀ {ξ₂ ξ₁ ξ : S.Hid.G},
      S.Hid.comp ξ₂ ξ₁ = some ξ →
      S.Hid.cost ξ = S.Hid.cost ξ₂ + S.Hid.cost ξ₁

  /-- Every hidden trace has a non-negative cost. -/
  cost_nonneg :
    ∀ (ξ : S.Hid.G), 0 ≤ S.Hid.cost ξ

  /--
  Structural Independence (Section 8):
  The spend functional and the defect allowance are structurally independent.
  Ensures that the thermodynamic penalty cannot be trivially zeroed out.
  -/
  structural_independence :
    ∃ (R : S.Obs.V), delta S R > 0

/-- Structure to package a system and its verified assumptions. -/
structure VerifiedSystem where
  sys : System
  asm : Assumptions sys

/-- Extended structure for systems that are explicitly segmentable. -/
structure SegmentableAssumptions (S : System) extends Assumptions S, Segmentable S

structure VerifiedSegmentableSystem where
  sys : System
  asm : SegmentableAssumptions sys

end Coh.V2

