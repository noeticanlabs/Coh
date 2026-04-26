import Coh.V2.Analytic
import Mathlib.Data.Rat.Lemmas

/-! Helper lemmas for ℚ → ℝ casts -/
private lemma ratCast_add_real (a b : ℚ) :
    ((a + b : ℚ) : ℝ) = (a : ℝ) + (b : ℝ) := by
  norm_num

private lemma ratCast_add_real_comm (a b : ℚ) :
    ((b + a : ℚ) : ℝ) = (a : ℝ) + (b : ℝ) := by
  norm_num [add_comm, add_left_comm, add_assoc]

private lemma zero_ratCast : (0 : ℝ) = (0 : ℚ) := by
  norm_num

/-!
## Coh V2 Certified Morphisms

This module formalizes the concept of certified morphisms in the Coh V2 framework.
A certified morphism binds an observable trace to a cost-defect pair that
satisfies the fundamental Coh inequality and is dominated by the analytic envelope.
-/

namespace Coh.V2

universe u v

/--
A certified morphism carries an observable trace, a spend, and a defect bound,
together with the governing inequality and domination of the analytic envelope.
-/
structure CertifiedMor (S : System) (A : Assumptions S) {X : Type v} (V : X → ℚ) (x y : X) where
  trace : S.Obs.V
  spend : ℚ
  defect : ℚ
  spend_nonneg : 0 ≤ spend
  defect_nonneg : 0 ≤ defect
  law : V y + spend ≤ V x + defect
  defect_bound : delta S trace ≤ (defect : ℝ)

attribute [simp] CertifiedMor.trace CertifiedMor.spend CertifiedMor.defect

/-- Extension theorem for certified morphisms. -/
@[ext]
theorem CertifiedMor.ext {S : System} {A : Assumptions S} {X : Type v} {V : X → ℚ}
    {x y : X}
    {f g : CertifiedMor S A V x y}
    (htrace : f.trace = g.trace)
    (hspend : f.spend = g.spend)
    (hdefect : f.defect = g.defect) :
    f = g := by
  cases f
  cases g
  subst htrace hspend hdefect
  rfl

/-- Identity certified morphism. -/
def idMor {S : System} {A : Assumptions S} {X : Type v} (V : X → ℚ) (x : X) :
    CertifiedMor S A V x x where
  trace := S.Obs.id
  spend := 0
  defect := 0
  spend_nonneg := le_rfl
  defect_nonneg := le_rfl
  law := by simp only [add_zero, le_refl]
  defect_bound := by
    simpa using (delta_id (S := S) A).le

/-- Composition of certified morphisms - requires SegmentableAssumptions for subadditivity. -/
def compose {S : System} (A : SegmentableAssumptions S) {X : Type v} (V : X → ℚ)
    {x y z : X}
    (f : CertifiedMor S A.toAssumptions V x y)
    (g : CertifiedMor S A.toAssumptions V y z)
    {R₂₁ : S.Obs.V}
    (hcomp : S.Obs.comp g.trace f.trace = some R₂₁) :
    CertifiedMor S A.toAssumptions V x z where
  trace := R₂₁
  spend := f.spend + g.spend
  defect := f.defect + g.defect
  spend_nonneg := add_nonneg f.spend_nonneg g.spend_nonneg
  defect_nonneg := add_nonneg f.defect_nonneg g.defect_nonneg
  law := by
    linarith [f.law, g.law]
  defect_bound := by
    calc
      delta S R₂₁ ≤ delta S g.trace + delta S f.trace := delta_subadd A hcomp
      _ ≤ (g.defect : ℝ) + (f.defect : ℝ) := add_le_add g.defect_bound f.defect_bound
      _ = ((f.defect + g.defect : ℚ) : ℝ) := by
        simpa [add_comm] using (ratCast_add_real (a := f.defect) (b := g.defect)).symm

theorem assoc_certified {S : System} (A : SegmentableAssumptions S) {X : Type v} (V : X → ℚ)
    {w x y z : X}
    (f : CertifiedMor S A.toAssumptions V w x) (g : CertifiedMor S A.toAssumptions V x y) (h : CertifiedMor S A.toAssumptions V y z)
    {R12 R23 R123a R123b : S.Obs.V}
    (h12 : S.Obs.comp g.trace f.trace = some R12)
    (h23 : S.Obs.comp h.trace g.trace = some R23)
    (h123a : S.Obs.comp h.trace R12 = some R123a)
    (h123b : S.Obs.comp R23 f.trace = some R123b) :
    compose A V (compose A V f g h12) h h123a = compose A V f (compose A V g h h23) h123b := by
  apply CertifiedMor.ext
  · have h_eq := A.toAssumptions.obs_assoc h12 h23 h123a
    rw [h123b] at h_eq
    injection h_eq with h_eq
    exact h_eq.symm
  · simp [compose, add_assoc]
  · simp [compose, add_assoc]

theorem id_right_certified {S : System} (A : SegmentableAssumptions S) {X : Type v} (V : X → ℚ)
    {x y : X} (f : CertifiedMor S A.toAssumptions V x y)
    {R : S.Obs.V} (h : S.Obs.comp f.trace S.Obs.id = some R) :
    compose A V (idMor V x) f h = f := by
  apply CertifiedMor.ext
  · have h_id := A.toAssumptions.obs_id_right f.trace
    rw [h] at h_id
    injection h_id
  · simp [compose, idMor]
  · simp [compose, idMor]

theorem id_left_certified {S : System} (A : SegmentableAssumptions S) {X : Type v} (V : X → ℚ)
    {x y : X} (f : CertifiedMor S A.toAssumptions V x y)
    {R : S.Obs.V} (h : S.Obs.comp S.Obs.id f.trace = some R) :
    compose A V f (idMor V y) h = f := by
  apply CertifiedMor.ext
  · have h_id := A.toAssumptions.obs_id_left f.trace
    rw [h] at h_id
    injection h_id
  · simp [compose, idMor]
  · simp [compose, idMor]

end Coh.V2
