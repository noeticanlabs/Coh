import Coh.V2.Analytic
import Mathlib.Data.Real.Basic

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
  cases htrace
  cases hspend
  cases hdefect
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
    simpa [delta_id A]

/--
`id_certified` mirrors the manuscript lemma:
the identity datum is certified because it is constructed as a `CertifiedMor`.
-/
def id_certified {S : System} {A : Assumptions S} {X : Type v} (V : X → ℝ) (x : X) :
    CertifiedMor S A V x x :=
  idMor V x

/--
Composition of certified morphisms.
This corresponds to the manuscript definition of certified composition.
-/
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
    have hδ : delta S R₂₁ ≤ delta S f.trace + delta S g.trace :=
      delta_subadd A hcomp
    have hb : delta S f.trace + delta S g.trace ≤ f.defect + g.defect :=
      add_le_add f.defect_bound g.defect_bound
    exact hδ.trans hb

/--
`compose_certified` mirrors the manuscript lemma:
the composite datum is certified because `compose` returns a `CertifiedMor`.
-/
def compose_certified {S : System} {A : Assumptions S} {X : Type v} (V : X → ℝ)
    {x y z : X}
    (f : CertifiedMor S A V x y)
    (g : CertifiedMor S A V y z)
    {R₂₁ : S.Obs.V}
    (hcomp : S.Obs.comp g.trace f.trace = some R₂₁) :
    CertifiedMor S A V x z :=
  compose V f g hcomp

end Coh.V2
