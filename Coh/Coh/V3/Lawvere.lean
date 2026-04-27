import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Coh.V2.Definitions

/-!
## Coh V3 Lawvere Enrichment (Rational Version)

Strictly rational version of Lawvere enrichment to ensure computational determinism.
-/

namespace Coh.V3

universe u v

open CategoryTheory Coh.V2

/--
  Lawvere Enrichment over the Extended Non-negative Rationals (ENNRat).
  This provides a strictly rational foundation for metric enrichment.
-/
class LawvereEnriched (C : Type u) [Category C] where
  dist {X Y : C} : (X ⟶ Y) → (X ⟶ Y) → ENNRat
  dist_self {X Y : C} (f : X ⟶ Y) : dist f f = 0
  dist_triangle {X Y : C} (f g h : X ⟶ Y) : dist f h ≤ dist f g + dist g h
  dist_comp {X Y Z : C} (f f' : X ⟶ Y) (g g' : Y ⟶ Z) :
    dist (f ≫ g) (f' ≫ g') ≤ dist f f' + dist g g'

namespace LawvereEnriched
variable {C : Type u} [Category C] [LawvereEnriched C]
@[simp] theorem dist_id_self {X Y : C} (f : X ⟶ Y) : dist f f = 0 := dist_self f
end LawvereEnriched

instance LawvereEnrichedDiscrete (α : Type u) : LawvereEnriched (Discrete α) where
  dist := fun _ _ => 0
  dist_self := fun _ => rfl
  dist_triangle := fun _ _ _ => zero_le _
  dist_comp := fun _ _ _ _ => zero_le _

end Coh.V3

