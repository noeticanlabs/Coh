import Coh.V2.Definitions
import Mathlib.Order.Bounds.Basic

/-!
## Coh V2 Axiomatic Framework

This module formalizes the core axioms of the Coh V2 framework using strict rational types.
-/

namespace Coh.V2

universe u

/--
Frozen Coh V2 assumptions (Rational-Only).

These are the specification-level assumptions mirrored from the manuscript,
now hardened to use strictly rational defect envelopes.
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

  /-- Left identity relative to the `comp S.Obs.id R` convention. -/
  obs_id_left :
    ∀ (R : S.Obs.V), S.Obs.comp S.Obs.id R = some R

  /-- Every observable trace has at least one hidden witness. -/
  fiber_nonempty :
    ∀ (R : S.Obs.V), (Fiber S R).Nonempty

  /--
    The sealed delta is indeed an upper bound for the cost of any hidden witness
    in the fiber. This replaces the supremum-based analytic definition.
  -/
  delta_le :
    ∀ {R : S.Obs.V} {ξ : S.Hid.G}, ξ ∈ Fiber S R → S.Hid.cost ξ ≤ S.delta R

  /-- The delta at the identity observable must be zero. -/
  delta_id :
    S.delta S.Obs.id = 0

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

  /-- The defect envelope must be non-negative for all observable traces. -/
  delta_nonneg :
    ∀ (R : S.Obs.V), 0 ≤ S.delta R

  /--
    Subadditivity of the defect envelope under observable composition.
    This ensures that the cost of a composite trace is bounded by the sum of its parts.
  -/
  delta_subadd :
    ∀ {R₁ R₂ R₂₁ : S.Obs.V},
      S.Obs.comp R₂ R₁ = some R₂₁ →
      S.delta R₂₁ ≤ S.delta R₂ + S.delta R₁

  /--
    Structural Independence (Section 8):
    Ensures that the thermodynamic penalty cannot be trivially zeroed out.
  -/
  structural_independence :
    ∃ (R : S.Obs.V), S.delta R > 0

  /-- Compositional Reachability ensures distance composition is well-defined. -/
  comp_reachable :
    ∀ {R₁ R₂ R₃ Ra Rb},
      S.Obs.comp Ra R₁ = some R₂ →
      S.Obs.comp Rb R₂ = some R₃ →
      ∃ Rc, S.Obs.comp Rb Ra = some Rc

/-- Structure to package a system and its verified assumptions. -/
structure VerifiedSystem where
  sys : System
  asm : Assumptions sys

/-- Extended structure for systems that are explicitly segmentable. -/
structure SegmentableAssumptions (S : System) extends Assumptions S, Segmentable S

structure VerifiedSegmentableSystem where
  sys : System
  asm : SegmentableAssumptions S

end Coh.V2
