import Coh.V2.Certified
import Mathlib.Order.Basic

/-!
## Coh V2 Category Theory

This module formalizes the category-theoretic structure of certified morphisms.
It proves that certified morphisms form a locally preordered category,
satisfying associativity and identity laws.
-/

noncomputable section

namespace Coh.V2

universe u v w

-- All parameters passed explicitly, no nested sections
-- to avoid Lean implicit resolution conflicts.

/-- Local defect-comparison preorder on a fixed hom-set. -/
def HomLE (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    {x y : X}
    (f g : Coh.V2.CertifiedMor S A V x y) : Prop :=
  f.trace = g.trace ∧ f.spend = g.spend ∧ f.defect ≤ g.defect

instance instHomPartialOrder (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ) {x y : X} :
    PartialOrder (Coh.V2.CertifiedMor S A V x y) where
  le f g := HomLE S A X V f g
  le_refl f := ⟨rfl, rfl, le_rfl⟩
  le_trans f g h hfg hgh := 
    ⟨hfg.1.trans hgh.1, hfg.2.1.trans hgh.2.1, hfg.2.2.trans hgh.2.2⟩
  le_antisymm f g hfg hgf := by
    apply CertifiedMor.ext
    · exact hfg.1
    · exact hfg.2.1
    · exact le_antisymm hfg.2.2 hgf.2.2

/-- Associativity of certified composition. -/
theorem assoc_certified
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    {w x y z : X}
    (f : Coh.V2.CertifiedMor S A V w x)
    (g : Coh.V2.CertifiedMor S A V x y)
    (h : Coh.V2.CertifiedMor S A V y z)
    {R₂₁ R₃₂ R₃₂₁a R₃₂₁b : S.Obs.V}
    (h₁₂ : S.Obs.comp g.trace f.trace = some R₂₁)
    (h₂₃ : S.Obs.comp h.trace g.trace = some R₃₂)
    (h₁₂₃a : S.Obs.comp h.trace R₂₁ = some R₃₂₁a)
    (h₁₂₃b : S.Obs.comp R₃₂ f.trace = some R₃₂₁b) :
    Coh.V2.compose V (Coh.V2.compose V f g h₁₂) h h₁₂₃a =
    Coh.V2.compose V f (Coh.V2.compose V g h h₂₃) h₁₂₃b := by
  apply CertifiedMor.ext
  · have h_assoc := Assumptions.obs_assoc A h₁₂ h₂₃ h₁₂₃a
    rw [h_assoc] at h₁₂₃b
    injection h₁₂₃b
  · simp [compose, add_assoc]
  · simp [compose, add_assoc]

/-- Identity laws for certified composition. -/
theorem id_right_certified
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    {x y : X} (f : Coh.V2.CertifiedMor S A V x y)
    {R : S.Obs.V} (hcomp : S.Obs.comp f.trace S.Obs.id = some R) :
    Coh.V2.compose V (idMor V x) f hcomp = f := by
  apply CertifiedMor.ext
  · have h_id := Assumptions.obs_id_right A f.trace
    rw [h_id] at hcomp
    injection hcomp
  · simp [compose, idMor]
  · simp [compose, idMor]

theorem id_left_certified
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    {x y : X} (f : Coh.V2.CertifiedMor S A V x y)
    {R : S.Obs.V} (hcomp : S.Obs.comp S.Obs.id f.trace = some R) :
    Coh.V2.compose V f (idMor V y) hcomp = f := by
  apply CertifiedMor.ext
  · have h_id := Assumptions.obs_id_left A f.trace
    rw [h_id] at hcomp
    injection hcomp
  · simp [compose, idMor]
  · simp [compose, idMor]

/-- A category where each hom-set is a local preorder. -/
structure LocalPreorderCategory (Obj : Type u) where
  Hom : Obj → Obj → Type w
  id : ∀ x, Hom x x
  comp : ∀ {x y z}, Hom x y → Hom y z → Hom x z
  comp_assoc :
    ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z),
      comp (comp f g) h = comp f (comp g h)
  id_right : ∀ {x y} (f : Hom x y), comp (id x) f = f
  id_left : ∀ {x y} (f : Hom x y), comp f (id y) = f
  /-- Local preorder on each hom-set. -/
  homPreorder : ∀ {x y : Obj}, PartialOrder (Hom x y)
  /-- Composition is monotone in both arguments. -/
  comp_monotone :
    ∀ {x y z} {f₁ f₂ : Hom x y} {g₁ g₂ : Hom y z},
      (f₁ ≤ f₂) → (g₁ ≤ g₂) → comp f₁ g₁ ≤ comp f₂ g₂

/-- The certified category packaged as an explicit object. -/
def certifiedCategory
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    (chooseComp :
      ∀ {x y z : X}
        (f : Coh.V2.CertifiedMor S A V x y)
        (g : Coh.V2.CertifiedMor S A V y z),
        Σ' R₂₁ : S.Obs.V, S.Obs.comp g.trace f.trace = some R₂₁) :
    LocalPreorderCategory X :=
  let idObj : ∀ x : X, Coh.V2.CertifiedMor S A V x x :=
    fun x => idMor (S := S) (A := A) (X := X) V x
  let compObj :
      ∀ {x y z : X},
        Coh.V2.CertifiedMor S A V x y →
        Coh.V2.CertifiedMor S A V y z →
      Coh.V2.CertifiedMor S A V x z :=
    fun {x y z} f g =>
      let p := chooseComp f g
      compose (S := S) (A := A) (X := X) V f g p.2
  have id_right_law : ∀ {x y : X} (f : Coh.V2.CertifiedMor S A V x y),
      compObj (idObj x) f = f := by
    intro x y f
    let p := chooseComp (idObj x) f
    apply id_right_certified S A X V f p.2
  have id_left_law : ∀ {x y : X} (f : Coh.V2.CertifiedMor S A V x y),
      compObj f (idObj y) = f := by
    intro x y f
    let p := chooseComp f (idObj y)
    apply id_left_certified S A X V f p.2
  have assoc_law : ∀ {w x y z : X}
      (f : Coh.V2.CertifiedMor S A V w x)
      (g : Coh.V2.CertifiedMor S A V x y)
      (h : Coh.V2.CertifiedMor S A V y z),
      compObj (compObj f g) h = compObj f (compObj g h) := by
    intro w x y z f g h
    let p₁₂ := chooseComp f g
    let p₂₃ := chooseComp g h
    let p₁₂₃a := chooseComp (compObj f g) h
    let p₁₂₃b := chooseComp f (compObj g h)
    apply assoc_certified S A X V f g h p₁₂.2 p₂₃.2 p₁₂₃a.2 p₁₂₃b.2
  have comp_monotone_law : ∀ {x y z : X} {f₁ f₂ : Coh.V2.CertifiedMor S A V x y} {g₁ g₂ : Coh.V2.CertifiedMor S A V y z},
      (f₁ ≤ f₂) → (g₁ ≤ g₂) → compObj f₁ g₁ ≤ compObj f₂ g₂ := by
    intro x y z f1 f2 g1 g2 hf hg
    rcases hf with ⟨htf, hsf, hdf⟩
    rcases hg with ⟨htg, hsg, hdg⟩
    let p1 := chooseComp f1 g1
    let p2 := chooseComp f2 g2
    constructor
    · simp [compObj, compose]
      have htr1 := p1.2
      have htr2 := p2.2
      rw [htf, htg] at htr1
      exact Option.some.inj (htr1.symm.trans htr2)
    · constructor
      · simp [compObj, compose, hsf, hsg]
      · simp [compObj, compose]
        exact add_le_add hdf hdg
  { Hom := fun x y => Coh.V2.CertifiedMor S A V x y,
    id := idObj,
    comp := compObj,
    comp_assoc := assoc_law,
    id_right := id_right_law,
    id_left := id_left_law,
    homPreorder := fun {x y} => instHomPartialOrder S A X V,
    comp_monotone := comp_monotone_law }

/-- The main theorem: certified morphisms determine a locally preordered category. -/
theorem certified_category
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    (chooseComp :
      ∀ {x y z : X}
        (f : Coh.V2.CertifiedMor S A V x y)
        (g : Coh.V2.CertifiedMor S A V y z),
        Σ' R₂₁ : S.Obs.V, S.Obs.comp g.trace f.trace = some R₂₁) :
    Nonempty (LocalPreorderCategory.{v, 0} X) := by
  exact ⟨certifiedCategory S A X V chooseComp⟩

end Coh.V2
