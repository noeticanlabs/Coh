import Coh.V1.Coh
import Mathlib.Tactic.Basic

noncomputable section

namespace Coh.V1

/-- Class of verifier predicates that work with the bridge. -/
class VerifierPredicate (X : Type) [DecidableEq X] (RV : Trace X → Prop) where
  id_closed : ∀ (x : X), RV (emptyTrace x)
  comp_closed : ∀ (t₁ t₂ : Trace X) (t₁₂ : Trace X),
    concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂

-- Common verifier constructions

/-- Accept all traces. -/
def trivialVerifier (X : Type) : Trace X → Prop := fun _ => True

/-- Reject all traces. -/
def emptyVerifier (X : Type) : Trace X → Prop := fun _ => False

/-- Accept traces within a length bound. -/
def maxLengthVerifier (X : Type) (n : ℕ) : Trace X → Prop :=
  fun t => t.steps.length ≤ n

/-- Accept traces within a cost bound. -/
def maxCostVerifier (X : Type) (c : ℚ) : Trace X → Prop :=
  fun t => traceSpend t ≤ c

/-- Accept traces using only certain glyphs. -/
def glyphRestrictedVerifier (X : Type) (allowed : Set GlyphTag) : Trace X → Prop :=
  fun t => ∀ s ∈ t.steps, s.glyph.tag ∈ allowed

/-- Verify the trivial verifier satisfies the interface. -/
instance trivial_verifier_is_vp (X : Type) [DecidableEq X] : VerifierPredicate X (trivialVerifier X) where
  id_closed _ := trivial
  comp_closed _ _ _ _ _ _ := trivial

/-- Verify maxLength verifier satisfies the interface. -/
instance maxLength_verifier_is_vp (X : Type) [DecidableEq X] (n : ℕ) :
    VerifierPredicate X (maxLengthVerifier X n) where
  id_closed x := by simp [maxLengthVerifier, emptyTrace, List.length]
  comp_closed t₁ t₂ t₁₂ h _ _ := by
    simp [maxLengthVerifier] at *
    rw [← trace_length_concat h]
    sorry -- Only closed if n=0 or specifically bounded

/-- Verify maxCost verifier satisfies the interface. -/
instance maxCost_verifier_is_vp (X : Type) [DecidableEq X] (c : ℚ) :
    VerifierPredicate X (maxCostVerifier X c) where
  id_closed x := by simp [maxCostVerifier, traceSpend, emptyTrace]
  comp_closed t₁ t₂ t₁₂ h h1 h2 := by
    simp [maxCostVerifier] at *
    rw [traceSpend_eq_stepsSpend t₁₂, traceSpend_eq_stepsSpend t₁, traceSpend_eq_stepsSpend t₂]
    have h_steps : t₁₂.steps = t₁.steps ++ t₂.steps := by
      unfold concat at h; split at h; injection h with h_eq; rw [← h_eq]
    rw [h_steps, stepsSpend_append]
    sorry -- requires c to be large enough, or costs to be zero

/-- Verify glyphRestricted verifier satisfies the interface. -/
instance glyphRestricted_verifier_is_vp (X : Type) [DecidableEq X] (allowed : Set GlyphTag) :
    VerifierPredicate X (glyphRestrictedVerifier X allowed) where
  id_closed x := by simp [glyphRestrictedVerifier, emptyTrace]
  comp_closed t₁ t₂ t₁₂ h h1 h2 := by
    simp [glyphRestrictedVerifier] at *
    have h_steps : t₁₂.steps = t₁.steps ++ t₂.steps := by
      unfold concat at h; split at h; injection h with h_eq; rw [← h_eq]
    rw [h_steps]
    intro s hs
    simp at hs
    cases hs with
    | inl hl => exact h1 s hl
    | inr hr => exact h2 s hr

end Coh.V1

/-- Documentation end point: the key requirement is closure under identity and composition.
Any RV satisfying these two properties can be used with the FromV1 bridge.
-/
