import Coh.V2.Certified
import Mathlib.Order.Basic

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

instance instHomPreorder (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ) {x y : X} :
    Preorder (Coh.V2.CertifiedMor S A V x y) where
  le f g := HomLE S A X V f g
  le_refl f := by
    exact ⟨rfl, rfl, le_rfl⟩
  le_trans f g h hfg hgh := by
    rcases hfg with ⟨htr₁, hsp₁, hd₁⟩
    rcases hgh with ⟨htr₂, hsp₂, hd₂⟩
    exact ⟨htr₁.trans htr₂, hsp₁.trans hsp₂, le_trans hd₁ hd₂⟩

/-- Associativity of certified composition. -/
theorem assoc_certified
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    {w x y z : X}
    (f : Coh.V2.CertifiedMor S A V w x)
    (g : Coh.V2.CertifiedMor S A V x y)
    (h : Coh.V2.CertifiedMor S A V y z)
    {R₁₂ R₂₃ R₁₂₃ : S.Obs.V}
    (h₁₂ : S.Obs.comp g.trace f.trace = some R₁₂)
    (h₂₃ : S.Obs.comp h.trace g.trace = some R₂₃)
    (h₁₂₃a : S.Obs.comp h.trace R₁₂ = some R₁₂₃)
    (h₁₂₃b : S.Obs.comp R₂₃ f.trace = some R₁₂₃) :
    Coh.V2.compose (S := S) (A := A) (X := X) V
      (Coh.V2.compose (S := S) (A := A) (X := X) V f g h₁₂) h h₁₂₃a =
      Coh.V2.compose (S := S) (A := A) (X := X) V
        f (Coh.V2.compose (S := S) (A := A) (X := X) V g h h₂₃) h₁₂₃b := by
  ext
  · rfl
  · simp [Coh.V2.compose, add_assoc, add_comm, add_left_comm]
  · simp [Coh.V2.compose, add_assoc, add_comm, add_left_comm]

/-- Identity laws for certified composition. -/
theorem identity_laws
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    {x y : X}
    (f : Coh.V2.CertifiedMor S A V x y) :
    Coh.V2.compose (S := S) (A := A) (X := X) V
      (Coh.V2.idMor (S := S) (A := A) (X := X) V x) f
      (Assumptions.obs_id_right A f.trace) = f ∧
    Coh.V2.compose (S := S) (A := A) (X := X) V
      f (Coh.V2.idMor (S := S) (A := A) (X := X) V y)
      (Assumptions.obs_id_left A f.trace) = f := by
  constructor
  · ext
    · simp [Coh.V2.compose, Assumptions.obs_id_right A]
    · simp [Coh.V2.compose, Coh.V2.idMor]
    · simp [Coh.V2.compose, Coh.V2.idMor]
  · ext
    · simp [Coh.V2.compose, Assumptions.obs_id_left A]
    · simp [Coh.V2.compose, Coh.V2.idMor]
    · simp [Coh.V2.compose, Coh.V2.idMor]

/-- Monotonicity of certified composition. -/
theorem compose_monotone
    (S : System) (A : Assumptions S) (X : Type v) (V : X → ℝ)
    {x y z : X}
    {f f' : Coh.V2.CertifiedMor S A V x y}
    {g g' : Coh.V2.CertifiedMor S A V y z}
    (hf : HomLE S A X V f f')
    (hg : HomLE S A X V g g')
    {R₂₁ : S.Obs.V}
    (hcomp : S.Obs.comp g.trace f.trace = some R₂₁) :
    let hcomp' : S.Obs.comp g'.trace f'.trace = some R₂₁ := by
      rcases hf with ⟨hftr, _, _⟩
      rcases hg with ⟨hgtr, _, _⟩
      simpa [hftr, hgtr] using hcomp
    HomLE S A X V
      (Coh.V2.compose (S := S) (A := A) (X := X) V f g hcomp)
      (Coh.V2.compose (S := S) (A := A) (X := X) V f' g' hcomp') := by
  rcases hf with ⟨hftr, hfsp, hfd⟩
  rcases hg with ⟨hgtr, hgsp, hgd⟩
  dsimp only []
  refine ⟨rfl, ?_, ?_⟩
  · simpa [Coh.V2.compose, hfsp, hgsp]
  · simpa [Coh.V2.compose] using add_le_add hfd hgd

/-- A small concrete structure for a locally preordered category. -/
structure LocalPreorderCategory (Obj : Type u) where
  Hom : Obj → Obj → Type w
  id : ∀ x, Hom x x
  comp : ∀ {x y z}, Hom x y → Hom y z → Hom x z
  comp_assoc :
    ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z),
      comp (comp f g) h = comp f (comp g h)
  id_right : ∀ {x y} (f : Hom x y), comp (id x) f = f
  id_left : ∀ {x y} (f : Hom x y), comp f (id y) = f

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
    fun x => Coh.V2.idMor (S := S) (A := A) (X := X) V x
  let compObj :
      ∀ {x y z : X},
        Coh.V2.CertifiedMor S A V x y →
        Coh.V2.CertifiedMor S A V y z →
      Coh.V2.CertifiedMor S A V x z :=
    fun {x y z} f g =>
      let p := chooseComp f g
      Coh.V2.compose (S := S) (A := A) (X := X) V f g p.2
  have id_right : ∀ {x y : X} (f : Coh.V2.CertifiedMor S A V x y),
      compObj (idObj x) f = f := by
    intro x y f
    let p := chooseComp (idObj x) f
    ext
    · have hp : S.Obs.comp f.trace S.Obs.id = some p.1 := by
        simpa [idObj] using p.2
      have hid : S.Obs.comp f.trace S.Obs.id = some f.trace :=
        Assumptions.obs_id_right A f.trace
      exact Option.some.inj (hp.symm.trans hid)
    · simp [compObj, idObj, p, Coh.V2.compose, Coh.V2.idMor]
    · simp [compObj, idObj, p, Coh.V2.compose, Coh.V2.idMor]
  have id_left : ∀ {x y : X} (f : Coh.V2.CertifiedMor S A V x y),
      compObj f (idObj y) = f := by
    intro x y f
    let p := chooseComp f (idObj y)
    ext
    · have hp : S.Obs.comp S.Obs.id f.trace = some p.1 := by
        simpa [idObj] using p.2
      have hid : S.Obs.comp S.Obs.id f.trace = some f.trace :=
        Assumptions.obs_id_left A f.trace
      exact Option.some.inj (hp.symm.trans hid)
    · simp [compObj, idObj, p, Coh.V2.compose, Coh.V2.idMor]
    · simp [compObj, idObj, p, Coh.V2.compose, Coh.V2.idMor]
  have comp_assoc : ∀ {w x y z : X}
      (f : Coh.V2.CertifiedMor S A V w x)
      (g : Coh.V2.CertifiedMor S A V x y)
      (h : Coh.V2.CertifiedMor S A V y z),
      compObj (compObj f g) h = compObj f (compObj g h) := by
    intro w x y z f g h
    let p₁₂ := chooseComp f g
    let p₂₃ := chooseComp g h
    let p₁₂₃a := chooseComp (compObj f g) h
    let p₁₂₃b := chooseComp f (compObj g h)
    ext
    · have h₁₂₃a' : S.Obs.comp h.trace p₁₂.1 = some p₁₂₃a.1 := by
        simpa [compObj, p₁₂] using p₁₂₃a.2
      have hleft : S.Obs.comp p₂₃.1 f.trace = some p₁₂₃a.1 :=
        Assumptions.obs_assoc A p₁₂.2 p₂₃.2 h₁₂₃a'
      have hright : S.Obs.comp p₂₃.1 f.trace = some p₁₂₃b.1 := by
        simpa [compObj, p₂₃] using p₁₂₃b.2
      exact Option.some.inj (hleft.symm.trans hright)
    · simp [compObj, Coh.V2.compose, add_assoc, add_comm, add_left_comm]
    · simp [compObj, Coh.V2.compose, add_assoc, add_comm, add_left_comm]
  { Hom := fun x y => Coh.V2.CertifiedMor S A V x y,
    id := idObj,
    comp := compObj,
    comp_assoc := comp_assoc,
    id_right := id_right,
    id_left := id_left }

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
