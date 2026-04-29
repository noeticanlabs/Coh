import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.Order
import Mathlib.Algebra.Order.Monoid.WithTop
import Coh.V2.Definitions

/-!
## Coh V3 Lemmas: ENNRat Arithmetic Properties

This module contains foundational lemmas for ENNRat arithmetic.
ENNRat is defined in V2.Definitions as `WithTop NNRat`.

## Notation Ledger
- `ENNRat` = WithTop NNRat (extended non-negative rationals)
- `NNRat` = non-negative rationals ℚ≥0
- `ℚ` = rationals

## Key Properties
1. ENNRat = NNRat ∪ {⊤} where ⊤ represents infinity
2. NNRat embeds into ENNRat via WithTop.some
3. Addition on ENNRat: ⊤ + x = ⊤, x + ⊤ = ⊤
4. Order on ENNRat extends NNRat order with ⊤ ≥ x

## Critical Lemmas
1. `ennrat_top_add` : ⊤ + x = ⊤
2. `ennrat_add_top` : x + ⊤ = ⊤
3. `ennrat_add_mono` : addition is monotone
4. `ennrat_ofRat_nonneg` : ofRat preserves non-negativity
-/

namespace Coh.V3

open ENNRat WithTop NNRat

/--
  Top element is absorbing for addition.
  [PROVED] by definition of WithTop addition.
-/
@[simp]
theorem ennrat_top_add (x : ENNRat) : ⊤ + x = ⊤ := top_add x

/--
  Top element absorbs from right.
  [PROVED] by definition of WithTop addition.
-/
@[simp]
theorem ennrat_add_top (x : ENNRat) : x + ⊤ = ⊤ := add_top x

/--
  Monotonicity: if a ≤ b then a + c ≤ b + c.
  [PROVED] using AddLeftMono.
-/
theorem ennrat_add_mono_left (a b c : ENNRat) (h : a ≤ b) : a + c ≤ b + c :=
  add_le_add_left h c

/--
  Monotonicity: if b ≤ c then a + b ≤ a + c.
  [PROVED] using AddRightMono.
-/
theorem ennrat_add_mono_right (a b c : ENNRat) (h : b ≤ c) : a + b ≤ a + c :=
  add_le_add_right h a

/--
  Addition is monotone in both arguments.
  [PROVED] by combining mono lemmas.
-/
theorem ennrat_add_mono (a b c d : ENNRat) (ha : a ≤ c) (hb : b ≤ d) : a + b ≤ c + d :=
  (ennrat_add_mono_left _ _ _ ha).trans (ennrat_add_mono_right _ _ _ hb)

/--
  Non-negativity preserved under ofRat.
  [PROVED] since ofRat returns non-negative values.
-/
theorem ennrat_ofRat_nonneg (q : ℚ) (hq : 0 ≤ q) : 0 ≤ ENNRat.ofRat q := by
  simp [ENNRat.ofRat, hq]

/--
  ofRat of a non-negative rational is not top.
  [PROVED] by definition of ofRat.
-/
theorem ennrat_ofRat_ne_top (q : ℚ) (hq : 0 ≤ q) : ENNRat.ofRat q ≠ ⊤ := by
  simp [ENNRat.ofRat, hq]
  split_ifs <;> simp

/--
  Top is greatest element.
  [PROVED] by WithTop property.
-/
theorem le_top (x : ENNRat) : x ≤ ⊤ := le_top x

end Coh.V3
