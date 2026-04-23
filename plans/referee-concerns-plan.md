# Plan to Address Referee Concerns

## Problem Statement

The Lean V2 formalization has several weak points that referees might flag:

1. **Missing concrete model** — The only model is the trivial `Unit` state with `True` verifier
2. **Finite-word example not formalized** — Manuscript Section 09 describes a concrete model that doesn't exist in Lean
3. **Bridge variants undocumented** — Three `FromV1*` files exist without clear relationship
4. **Cost type mismatch** — V1 uses ℚ, V2 uses ℝ, no explicit bridge

---

## Task 1: Create Finite-Word Model

### Purpose
Formalize the concrete instantiation from manuscript Section 09.

### Manuscript Specification
- Hidden alphabet: Σ = A × B (observable × hidden refinement)
- Observable alphabet: A (finite)
- Projection: erase hidden B-coordinate
- Cost: additive over hidden tags (c_B : B → ℝ≥0)
- Result: `defect(R) = |R| * c_max`

### Lean Implementation Plan

Create `Coh/Coh/V2/FiniteWord.lean`:

```lean
-- Parameters
variable (A : Type) [Fintype A] [DecidableEq A]
variable (B : Type) [Fintype B] [DecidableEq B]
variable (c_B : B → ℝ)

-- Hidden carrier: Σ*
def hiddenG := List (A × B)

-- Observable carrier: A*
def observableV := List A

-- Projection: erase B
def proj (ξ : hiddenG) : observableV := ξ.map Prod.fst

-- Hidden composition: concatenation
def hiddenComp (ξ₂ ξ₁ : hiddenG) : Option hiddenG := some (ξ₁ ++ ξ₂)

-- Hidden cost: sum of B-costs
def hiddenCost (ξ : hiddenG) : ℝ := ξ.map (c_B ∘ Prod.snd) |>.sum

-- Observable composition: concatenation
def obsComp (R₂ R₁ : observableV) : Option observableV := some (R₁ ++ R₂)

-- Observable identity: empty word
def obsId : observableV := []

-- Build System, prove all 7 axioms hold
```

### Proof Obligations
1. Observable associativity (by list append associativity)
2. Observable identity laws (by list identity)
3. Fiber nonemptiness (choose any B-sequence)
4. Fiber boundedness (fixed length + bounded tag costs)
5. Identity fiber zero-cost (empty word has cost 0)
6. Hidden cost additivity (by sum over concatenated list)
7. Fiber decomposition (by splitting list)

---

## Task 2: Create Non-Trivial Concrete Model

### Purpose
Go beyond trivial Unit model to demonstrate framework power.

### Option A: Two-State Model
States: `{ready, busy}` — simple but non-trivial

```lean
inductive State2
| ready
| busy

-- Define traces between these states
-- Define RV that accepts only valid state transitions
-- Prove certified_category exists
```

### Option B: Counter Model
States: ℕ (natural numbers) — infinite but simple

```lean
-- Increment/decrement steps
-- Potential: V(n) = n
-- This shows the framework handles unbounded state
```

### Option C: Use Finite-Word Model (recommended)
The finite-word model from Task 1 can serve as the non-trivial model:
- State space: List A (finite words as "states")
- Potential: length-based or custom
- This directly justifies the framework

---

## Task 3: Document RV Requirements

### Purpose
Clarify what properties the verifier predicate must satisfy.

### Current State
`FromV1.lean` requires:
```lean
RV : Trace X → Prop
hRV_id : ∀ x, RV (emptyTrace x)
hRV_comp : ∀ t₁ t₂ t₁₂, concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂
```

### Documentation Needed
Create `Coh/Coh/V2/FromV1/Lemmas.lean` or add to existing file:

```lean
/-- Class of verifier predicates that work with the V1→V2 bridge. -/
class VerifierPredicate (X : Type) [DecidableEq X] (RV : Trace X → Prop) where
  id_closed : ∀ x, RV (emptyTrace x)
  comp_closed : ∀ t₁ t₂ t₁₂, concat t₁ t₂ = some t₁₂ → RV t₁ → RV t₂ → RV t₁₂

/-- Common verifier constructions. -/
namespace VerifierPredicates

/-- Accept-all verifier (used in trivial model). -/
def trivial (X : Type) : Trace X → Prop := fun _ => True

/-- Accept-none verifier. -/
def empty (X : Type) : Trace X → Prop := fun _ => False

/-- Length-bounded verifier. -/
def maxLength (X : Type) (n : ℕ) : Trace X → Prop := 
  fun t => t.steps.length ≤ n

/-- Cost-bounded verifier. -/
def maxCost (X : Type) (c : ℚ) : Trace X → Prop :=
  fun t => traceSpend t ≤ c
```

---

## Task 4: Document Bridge Variants

### Purpose
Clarify relationship between:
- `FromV1.lean`
- `FromV1Degenerate.lean`
- `FromV1Quotient.lean`

### Analysis Required

| File | Purpose | When to Use |
|------|---------|-------------|
| FromV1.lean | Standard bridge | General case |
| FromV1Degenerate.lean | ? | Need to examine |
| FromV1Quotient.lean | ? | Need to examine |

### Action
1. Read each file's docstrings
2. Determine the distinguishing feature
3. Create `Coh/Coh/V2/FromV1/README.md` or add module docs

---

## Task 5: Create Cost Type Bridge (ℚ → ℝ)

### Purpose
Make explicit the relationship between V1's ℚ costs and V2's ℝ costs.

### Implementation Plan

Create `Coh/Coh/V2/CostBridge.lean`:

```lean
import Coh.V1.Coh
import Mathlib.Data.Real.Encodable

namespace Coh.V1

/-- Convert rational cost to real. -/
def ratToReal (q : ℚ) : ℝ := q

/-- Lift rational-valued function to real-valued. -/
def liftToReal {X : Type} (f : X → ℚ) : X → ℝ := ratToReal ∘ f

end Coh.V1

-- Prove compatibility lemmas:
theorem traceSpend_real {X : Type} (t : Trace X) :
    Coh.V1.ratToReal (traceSpend t) = traceSpend t := by rfl

theorem traceDefect_real {X : Type} (t : Trace X) :
    Coh.V1.ratToReal (traceDefect t) = traceDefect t := by rfl
```

---

## Execution Order

1. **Task 1** (Finite-word model) — Highest priority, addresses main gap
2. **Task 2** (Non-trivial model) — Can use Task 1 result
3. **Task 3** (RV documentation) — Independent
4. **Task 4** (Bridge docs) — Independent  
5. **Task 5** (Cost bridge) — Low priority, mostly cosmetic

---

## Notes

- All tasks should produce compilable Lean code
- Follow existing naming conventions in `Coh/Coh/V2/`
- Use `noncomputable` where needed (standard practice)
- Add docstrings to all new definitions and theorems