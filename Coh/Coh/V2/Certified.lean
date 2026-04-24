import Coh.V2.Analytic
import Mathlib.Data.Real.Basic

/-!
## Coh V2 Certified Morphisms

This module formalizes the concept of certified morphisms in the Coh V2 framework.
A certified morphism binds an observable trace to a cost-defect pair that
satisfies the fundamental Coh inequality and is dominated by the analytic envelope.
-/

noncomputable section

namespace Coh.V2

universe u v

/--
A certified morphism carries an observable trace, a spend, and a defect bound,
together with the governing inequality and domination of the analytic envelope.
-/
structure CertifiedMor (S : System) (A : Assumptions S) {X : Type v} (V : X → ℝ) (x y : X) where
  trace : S.Obs.V
  spend : ℝ
  defect : ℝ
  spend_nonneg : 0 ≤ spend
  defect_nonneg : 0 ≤ defect
  law : V y + spend ≤ V x + defect
  defect_bound : delta S trace ≤ defect

attribute [simp] CertifiedMor.trace CertifiedMor.spend CertifiedMor.defect

/-- Extension theorem for certified morphisms. -/
@[ext]
theorem CertifiedMor.ext {S : System} {A : Assumptions S} {X : Type v} {V : X → ℝ}
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
def idMor {S : System} {A : Assumptions S} {X : Type v} (V : X → ℝ) (x : X) :
    CertifiedMor S A V x x where
  trace := S.Obs.id
  spend := 0
  defect := 0
  spend_nonneg := le_rfl
  defect_nonneg := le_rfl
  law := by simp only [add_zero, le_refl]
  defect_bound := by
    simp only [delta_id A, le_refl]

/-- Composition of certified morphisms. -/
def compose {S : System} {A : Assumptions S} {X : Type v} (V : X → ℝ)
    {x y z : X}
    (f : CertifiedMor S A V x y)
    (g : CertifiedMor S A V y z)
    {R₂₁ : S.Obs.V}
    (hcomp : S.Obs.comp g.trace f.trace = some R₂₁) :
    CertifiedMor S A V x z where
  trace := R₂₁
  spend := f.spend + g.spend
  defect := f.defect + g.defect
  spend_nonneg := add_nonneg f.spend_nonneg g.spend_nonneg
  defect_nonneg := add_nonneg f.defect_nonneg g.defect_nonneg
  law := by
    have hf := f.law
    have hg := g.law
    linarith
  defect_bound := by
    have hδ : delta S R₂₁ ≤ delta S g.trace + delta S f.trace :=
      delta_subadd A hcomp
    have hb : delta S g.trace + delta S f.trace ≤ f.defect + g.defect := by
      linarith [f.defect_bound, g.defect_bound]
    exact hδ.trans hb

theorem assoc_certified {S : System} {A : Assumptions S} {X : Type v} (V : X → ℝ)
    {w x y z : X}
    (f : CertifiedMor S A V w x) (g : CertifiedMor S A V x y) (h : CertifiedMor S A V y z)
    {R12 R23 R123a R123b : S.Obs.V}
    (h12 : S.Obs.comp g.trace f.trace = some R12)
    (h23 : S.Obs.comp h.trace g.trace = some R23)
    (h123a : S.Obs.comp h.trace R12 = some R123a)
    (h123b : S.Obs.comp R23 f.trace = some R123b) :
    compose V (compose V f g h12) h h123a = compose V f (compose V g h h23) h123b := by
  apply CertifiedMor.ext
  · have h_eq := A.obs_assoc h12 h23 h123a
    rw [h123b] at h_eq
    injection h_eq with h_eq
    exact h_eq.symm
  · simp [compose, add_assoc]
  · simp [compose, add_assoc]

theorem id_right_certified {S : System} {A : Assumptions S} {X : Type v} (V : X → ℝ)
    {x y : X} (f : CertifiedMor S A V x y)
    {R : S.Obs.V} (h : S.Obs.comp f.trace S.Obs.id = some R) :
    compose V (idMor V x) f h = f := by
  apply CertifiedMor.ext
  · have h_id := A.obs_id_right f.trace
    rw [h] at h_id
    injection h_id with h_id
    exact h_id
  · simp [compose, idMor]
  · simp [compose, idMor]

theorem id_left_certified {S : System} {A : Assumptions S} {X : Type v} (V : X → ℝ)
    {x y : X} (f : CertifiedMor S A V x y)
    {R : S.Obs.V} (h : S.Obs.comp S.Obs.id f.trace = some R) :
    compose V f (idMor V y) h = f := by
  apply CertifiedMor.ext
  · have h_id := A.obs_id_left f.trace
    rw [h] at h_id
    injection h_id with h_id
    exact h_id
  · simp [compose, idMor]
  · simp [compose, idMor]

end Coh.V2
