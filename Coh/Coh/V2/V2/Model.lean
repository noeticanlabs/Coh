import Coh.V1.Coh
import Coh.V2.FromV1
import Coh.V2.Category

namespace Coh.V2.Model

/-- A trivial state space with one object. -/
def TrivialX := Unit
deriving instance DecidableEq for TrivialX

/-- The verifier that accepts everything. -/
def trivialRV (_ : Coh.V1.Trace TrivialX) : Prop := True

theorem trivialRV_id (x : TrivialX) : trivialRV (Coh.V1.emptyTrace x) := True.intro

theorem trivialRV_comp (t₁ t₂ t₁₂ : Coh.V1.Trace TrivialX) 
    (_ : Coh.V1.concat t₁ t₂ = some t₁₂) :
    trivialRV t₁ → trivialRV t₂ → trivialRV t₁₂ := fun _ _ => True.intro

noncomputable def trivialSystem := systemFromV1 TrivialX () trivialRV (trivialRV_id ())

noncomputable def trivialAssumptions := assumptionsFromV1 TrivialX () trivialRV trivialRV_id trivialRV_comp

/-- The constant zero potential function. -/
def zeroPotential (_ : TrivialX) : ℝ := 0

/-- 
A proof that in the trivial system, everything is composable.
This is used to satisfy the `chooseComp` requirement of the categorical closure.
-/
def trivialChooseComp {x y z : TrivialX}
    (f : CertifiedMor trivialSystem trivialAssumptions zeroPotential x y)
    (g : CertifiedMor trivialSystem trivialAssumptions zeroPotential y z) :
    Σ' R₂₁ : (observableSystemFromV1 TrivialX () trivialRV (trivialRV_id ())).V, 
      (observableSystemFromV1 TrivialX () trivialRV (trivialRV_id ())).comp g.trace f.trace = some R₂₁ := 
  let t1 := f.trace.1
  let t2 := g.trace.1
  let h_dst : t1.dst = t2.src := rfl
  let t12 : Coh.V1.Trace TrivialX := {
    src   := t1.src,
    dst   := t2.dst,
    steps := t1.steps ++ t2.steps,
    chain := Coh.V1.is_chain_concat t1.src t1.dst t2.dst t1.steps t2.steps t1.chain (by rw [h_dst]; exact t2.chain)
  }
  let R21 : (observableSystemFromV1 TrivialX () trivialRV (trivialRV_id ())).V := 
    ⟨t12, True.intro, rfl, rfl⟩
  ⟨R21, by
    simp [observableSystemFromV1, concat, h_dst, trivialRV]
    congr 1
    apply Subtype.ext
    simp [R21]
  ⟩

/-- The model existence proof: a certified category exists for TrivialX. -/
theorem trivial_category_exists :
    Nonempty (LocalPreorderCategory.{0, 0} TrivialX) := 
  Nonempty.intro (certifiedCategory trivialSystem trivialAssumptions TrivialX zeroPotential trivialChooseComp)

end Coh.V2.Model
