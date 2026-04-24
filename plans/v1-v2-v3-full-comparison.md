# Code Comparison: V1, V2, and V3 Formalizations

## Executive Summary

This document compares three versions of the Coh category formalization:

| Aspect | V1 | V2 | V3 |
|--------|-----|-----|-----|
| **Location** | `Coh/Coh/V1/Coh.lean` | `Coh/Coh/V2/*` | Manuscript PDFs |
| **Paradigm** | Operational/Concrete | Categorical/Abstract | Mathematical Exposition |
| **Focus** | Traces, RVAccept, Morphisms | Systems, Fibers, Delta | Theory, Proofs |
| **Status** | Single file (268 lines) | Multi-file (13 files) | Published PDFs |

---

## 1. Core Definitions Comparison

### 1.1 Type Structure

**V1** (`Coh/Coh/V1/Coh.lean`):
```
- GlyphTag (inductive): invoke, bind, route, guard, emit
- ControlToken: opcode, arg
- Glyph: tag, surface, token, wf_surface, wf_token
- Step X: src, dst, glyph, costSpend, costDefect, typed, compiles_ok
- Trace X: src, dst, steps, chain
- RVAccept: ∀s∈steps, s.typed
- CohMor X V x y: trace, src_eq, dst_eq, rv_ok, valid
```

**V2** (`Coh/Coh/V2/Primitive.lean`, `Definitions.lean`):
```
- HiddenSystem: G (Type), comp (G→G→Option G), cost (G→ℝ)
- ObservableSystem: V (Type), comp (V→V→Option V), id (V)
- System: Hid, Obs, proj
- Fiber S R: {ξ | proj ξ = R}
- CostSet S R: {c | ∃ξ∈Fiber, cost ξ = c}
- delta S R: sSup(CostSet S R)
- CertifiedMor S A V x y: trace, spend, defect, spend_nonneg, defect_nonneg, law, defect_bound
```

**V3** (Manuscript):
- Coh System: (X, K, V, Π, RV) tuples
- Hidden State: fiber of microscopic encodings
- Admissible Transition: RV-accepted + inequality satisfied

### 1.2 Key Structural Differences

| Aspect | V1 | V2 |
|--------|-----|-----|
| **Hidden Layer** | Implicit via glyphs | Explicit HiddenSystem structure |
| **Observable Layer** | Via traces only | Separate ObservableSystem |
| **Composition** | concat via Option | comp via Option |
| **Identity** | emptyTrace (singleton) | id field in ObservableSystem |
| **Verification** | RVAccept predicate | Assumptions structure |
| **Cost Function** | traceSpend, traceDefect | delta (envelope via sSup) |

---

## 2. Categorical Structures

### 2.1 Morphisms

**V1 CohMor** (lines 260-266):
- Combines trace + source/destination equalities + RVAccept + inequality law
- `law: V y + traceSpend ≤ V x + traceDefect`
- Single unified structure

**V2 CertifiedMor** (`Certified.lean` lines 22-29):
- Separates observable trace from cost parameters
- `law: V y + spend ≤ V x + defect`
- `defect_bound: delta S trace ≤ defect`
- Additional domination constraint

### 2.2 Composition Laws

**V1** (`concat` function, lines 120-128):
- Partial composition via Option
- Requires `t₁.dst = t₂.src`
- Theorems: assoc, id_right, id_left

**V2** (`compose` function, `Certified.lean` lines 60-81):
- Partial composition requiring `S.Obs.comp g.trace f.trace = some R₂₁`
- Additive: `spend = f.spend + g.spend`, `defect = f.defect + g.defect`
- Inherits V2 axioms for associativity and identity

### 2.3 Categorical Properties

**V1 Theorems** (verified in code):
- `is_chain_concat`: chain compositionality
- `concat_assoc`: associativity
- `concat_id_right`, `concat_id_left`: identity laws
- `rv_id`, `rv_comp`: verifier acceptance under composition

**V2 Structures** (`Category.lean`):
- `Slack2Cell`: 2-morphisms with delta slack
- `LocallyPosetal2Category`: 2-category with partial order hom-sets
- `semantic_initial`: initial object theorem
- Proves: `comp_assoc`, `id_right`, `id_left`, `comp_monotone`

---

## 3. Axiom Systems

### 3.1 V1 Implicit Axioms (in code)

From analyzing `Coh.lean` usage:
1. **RVAccept behavior**: All steps typed implies composed trace accepted
2. **Cost additivity**: `stepsSpend`/`stepsDefect` additive over concatenation
3. **Monotonicity**: Cost increases preserve inequality direction

### 3.2 V2 Explicit Axioms (`Axioms.lean` lines 24-82)

```lean
structure Assumptions (S : System) where
  obs_assoc        : ∀ R₁ R₂ R₃ R₁₂ R₂₃ R₁₂₃ ...
  obs_id_right    : ∀ R, S.Obs.comp R S.Obs.id = some R
  obs_id_left     : ∀ R, S.Obs.comp S.Obs.id R = some R
  fiber_nonempty  : ∀ R, (Fiber S R).Nonempty
  fiber_bounded  : ∀ R, BddAbove (CostSet S R)
  id_fiber_zero  : ∀ ξ ∈ Fiber S S.Obs.id, S.Hid.cost ξ = 0
  hidden_cost_add: ∀ ξ₂ ξ₁ ξ, S.Hid.comp ξ₂ ξ₁ = some ξ → cost ξ = cost ξ₂ + cost ξ₁
  fiber_decomp   : ∀ R₁ R₂ R₂₁ ξ, ...
  cost_nonneg    : ∀ ξ, 0 ≤ S.Hid.cost ξ
  structural_independence: ∃ R, delta S R > 0
```

### 3.3 V3 Mathematical Axioms (Manuscript)

From `Coh_Category_Manuscript.tex`:

1. **Verifier Filter** (Section 3): RV: X × Records × X → {ACCEPT, REJECT}
2. **Admissibility** (Definition 3.1): RV-accepted + thermodynamic inequality
3. **Oplax Bound** (Proposition 4.3): s(r₂∘r₁) ≤ s(r₁) + s(r₂)
4. **Telescoping Closure** (Theorem 5.1): Global boundary inequality

---

## 4. Cost Models

### 4.1 V1 Cost Model

```
- costSpend: ℚ (step→step additive)
- costDefect: ℚ (step→step additive)
- traceSpend t = stepsSpend t.steps
- traceDefect t = stepsDefect t.steps
- Inequality: V y + traceSpend ≤ V x + traceDefect
```

### 4.2 V2 Cost Model

```
- Hidden cost: ℝ (exact, additive)
- Delta envelope: δ(R) = sSup(CostSet R) via hidden witness supremum
- Certified spend: ℝ (observable, lower bound)
- Certified defect: ℝ (observable bound, ≥ δ)
- Inequality: V y + spend ≤ V x + defect
- Dominance: δ(R) ≤ defect
```

### 4.3 Key Theorems

**V2 Analytics** (`Analytic.lean`):
- `delta_id`: δ(id) = 0
- `delta_subadd`: δ(R₂₁) ≤ δ(R₂) + δ(R₁)
- `delta_nonneg`: 0 ≤ δ(R)

---

## 5. V1-to-V2 Bridge

### 5.1 Bridge Architecture (from plan file)

Per `plans/v1-to-v2-bridge-plan.md`:

```
Coh/V1/Coh.lean → (bridge) → Coh/V2/FromV1.lean → Coh/V2/Primitive.lean
                                              ↓
                           Coh/V2/...all V2 modules...
```

### 5.2 Translation Map

| V1 Concept | V2 Mapping |
|-----------|------------|
| Trace X | ObservableSystem.V / HiddenSystem.G |
| traceSpend | HiddenSystem.cost |
| RVAccept | Assumptions.fiber_nonempty |
| CohMor | CertifiedMor specialization |
| concat | Both comp operators |

### 5.3 Concrete Bridge (`FromV1.lean`)

The `Coh.V2.FromV1` module provides:

```lean
def hiddenSystem (X : Type) : HiddenSystem where
  G := Trace X
  comp := concat
  cost := fun t => (traceSpend t : ℝ)

def observableSystem (X : Type) : ObservableSystem where
  V := Trace X
  comp := concat
  id := emptyTrace ...

def system (X : Type) : System where
  Hid := hiddenSystem X
  Obs := observableSystem X
  proj := proj X
```

Proves `Assumptions` for this direct instantiation.

---

## 6. Instantiation Examples

### 6.1 V2 FiniteWord Model (`FiniteWord.lean`)

```
HiddenG A B := List (A × B)
ObservableV A := List A
proj ξ := ξ.map Prod.fst
hiddenCost c_B ξ := (ξ.map (fun p => c_B p.2)).sum
```

Provides full finite alphabet instantiation with costs.

---

## 7. Version Evolution Summary

```
                    ┌───────────────────────────────────────┐
                    │           V3 Manuscript               │
                    │   (Mathematical Exposition, PDFs)     │
                    └───────────────────────────────────────┘
                                         ↑
                    ┌────���──────────────────────────────────┐
                    │         V2 Categorical                │
                    │  (Systems, Fibers, Delta Envelope,   │
                    │   2-Category Structure, Assumptions)│
                    └───────────────────────────────────────┘
                    ↑ (bridge via FromV1.lean)
                    ┌───────────────────────────────────────┐
                    │          V1 Operational              │
                    │  (Glyphs, Traces, RVAccept,           │
                    │   Concrete Cost, Direct Inequality)  │
                    └───────────────────────────────────────┘
```

### 7.1 Key Evolution Points

| Stage | Innovation | Files |
|-------|------------|-------|
| **V1→V2** | Hidden/Observable separation | Primitive.lean |
| **V2** | Fiber + envelope construction | Definitions.lean, Analytic.lean |
| **V2** | Axiomatic framework | Axioms.lean |
| **V2** | 2-category structure | Category.lean |
| **V2** | Bridge instantiation | FromV1.lean, FiniteWord.lean |
| **V3** | Mathematical exposition | Manuscript.tex |

---

## 8. Pending Work (from existing plans)

### 8.1 From V1 Module Contract (`plans/from-v1-module-contract.md`)

- Replace V1 shims with bridge-backed definitions
- Re-express CohMor in terms of CertifiedMor

### 8.2 Manuscript Patch Plan (`plans/manuscript-patch-plan.md`)

- Explicit V1→V2 continuity section
- Add citation to formal Lean proof

### 8.3 Referee Concerns (`plans/referee-concerns-plan.md`)

- Address completeness concerns
- Verify all axioms required for theorems

---

## 9. Code Metrics

| Version | Files | Lines (approx) |
|--------|-------|----------------|
| V1 | 1 | 268 |
| V2 core | 13 | ~2000 |
| Bridge plans | 5+ | ~1000 |

---

## 10. Alignment Status

| V1 Concept | V2 Formalization | Manuscript | Status |
|-----------|----------------|------------|--------|
| Trace | ObservableSystem.V | Records | ✓ Mapped |
| Cost | delta envelope | Envelope Cost (Def 4.2) | ✓ Formalized |
| RVAccept | Assumptions.fiber_nonempty | RV filter | ✓ Abstracted |
| Inequality | CertifiedMor.law | Admissibility (Def 3.1) | ✓ Preserved |
| Composition | obs_assoc + comp | Oplax Bound (Prop 4.3) | ✓ Proven |

---

*Generated from code review of: Coh/Coh/V1/Coh.lean, Coh/Coh/V2/*.lean, Coh_Category_Manuscript.tex*