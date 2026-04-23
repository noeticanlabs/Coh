# V1 to V2 bridge plan

## Positioning

Treat [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) as the operational kernel and [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) through [`Coh/V2/Category.lean`](../Coh/V2/Category.lean) as the abstraction and closure layer built from that kernel.

In short:

- V1 = concrete execution and verifier semantics
- V2 = projection-aware categorical completion of V1

## Core architectural rule

V2 should no longer feel like an alternate foundation.

Instead, the dependency story should read:

- [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) defines traces, verifier acceptance, spend, defect, and the concrete transition law
- [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) stays generic and provides the abstract target interface that V1 will instantiate
- [`Coh/V2/Definitions.lean`](../Coh/V2/Definitions.lean) defines fibers and the envelope from those V1-derived objects
- [`Coh/V2/Analytic.lean`](../Coh/V2/Analytic.lean) proves the envelope facts
- [`Coh/V2/Certified.lean`](../Coh/V2/Certified.lean) packages certified transitions
- [`Coh/V2/Category.lean`](../Coh/V2/Category.lean) closes the construction categorically

## Lean dependency direction for [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean)

The correct dependency plan is **not**:

- [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) imports [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean)

That would make the V2 primitive layer look V1-specific and would collapse the abstraction boundary.

The correct plan is:

1. [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) remains generic and unchanged in role
2. [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) remains the concrete operational kernel
3. a new bridge file, preferably [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean), imports both [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) and [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean)
4. [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean) constructs a [`Coh.V2.HiddenSystem`](../Coh/V2/Primitive.lean:8), a [`Coh.V2.ObservableSystem`](../Coh/V2/Primitive.lean:14), and then a [`Coh.V2.System`](../Coh/V2/Primitive.lean:20) from V1 semantics
5. [`Coh/V2/Definitions.lean`](../Coh/V2/Definitions.lean), [`Coh/V2/Analytic.lean`](../Coh/V2/Analytic.lean), [`Coh/V2/Certified.lean`](../Coh/V2/Certified.lean), and [`Coh/V2/Category.lean`](../Coh/V2/Category.lean) should work over that instantiated system, not over a direct import edge from Primitive to V1

### Why this is the right direction

- [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean:1) is an abstract signature file
- [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean:1) is a concrete semantics file
- the bridge belongs in an instantiation layer, not in the abstract signature layer

This yields the dependency chain:

- [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean)
- [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean)
- [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean)
- [`Coh/V2/Definitions.lean`](../Coh/V2/Definitions.lean)
- [`Coh/V2/Analytic.lean`](../Coh/V2/Analytic.lean)
- [`Coh/V2/Certified.lean`](../Coh/V2/Certified.lean)
- [`Coh/V2/Category.lean`](../Coh/V2/Category.lean)

### What should move out of [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean)

Nothing mathematical needs to move out of [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean:1).

What changes is its interpretation:

- [`Coh.V2.HiddenSystem`](../Coh/V2/Primitive.lean:8) becomes the target shape for V1 hidden realizers
- [`Coh.V2.ObservableSystem`](../Coh/V2/Primitive.lean:14) becomes the target shape for V1 traces viewed observationally
- [`Coh.V2.System`](../Coh/V2/Primitive.lean:20) becomes the abstract package produced by the V1 bridge

### What should move into the bridge layer

The following should be defined in [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean), not in [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean):

- the concrete observable carrier built from [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38)
- the hidden witness carrier built from V1 verifier-realizing executions
- the projection from hidden witnesses to V1-visible traces
- the induced [`Coh.V2.System`](../Coh/V2/Primitive.lean:20) instance
- any proofs that V1 operations satisfy V2 assumptions

### Practical import policy

- [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) should import no V1 files
- [`Coh/V2/Definitions.lean`](../Coh/V2/Definitions.lean) should continue depending only on [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) unless a V1-specialized variant is created
- V1-specialized constructions should live in [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean) or sibling bridge files like [`Coh/V2/FromV1/Assumptions.lean`](../Coh/V2/FromV1/Assumptions.lean)
- if desired, a second namespace such as [`Coh.V2.FromV1`](../Coh/V2/FromV1.lean) should hold the instantiated objects to make the layering explicit

## Bridge map

### V1 operational objects

- [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38) becomes the observable-side carrier or the raw material for it
- [`Coh.V1.RVAccept`](../Coh/V1/Coh.lean:56) becomes realizability or fiber nonemptiness data
- [`Coh.V1.traceSpend`](../Coh/V1/Coh.lean:42) feeds certified spend
- [`Coh.V1.traceDefect`](../Coh/V1/Coh.lean:49) feeds explicit defect bounds or upper bounds compared to [`Coh.V2.delta`](../Coh/V2/Definitions.lean:21)
- [`Coh.V1.CohMor`](../Coh/V1/Coh.lean:66) becomes a wrapper or specialization of [`Coh.V2.CertifiedMor`](../Coh/V2/Certified.lean:14)

### V2 derived objects

- [`Coh.V2.System`](../Coh/V2/Primitive.lean:20) should be instantiated from V1 semantics
- [`Coh.V2.Fiber`](../Coh/V2/Definitions.lean:13) should be built from V1 hidden realizers projecting to a visible V1 trace
- [`Coh.V2.delta`](../Coh/V2/Definitions.lean:21) should be interpreted as the envelope induced by V1 hidden cost semantics
- [`Coh.V2.compose`](../Coh/V2/Certified.lean:65) and [`Coh.V2.idMor`](../Coh/V2/Certified.lean:42) should supply V1 composition and identity once the bridge exists

## Required refactors

1. Refactor [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38) so it carries enough endpoint structure to support categorical composition cleanly
2. Add a bridge module, preferably [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean), that interprets V1 operational data as a V2 system without changing the generic role of [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean)
3. Replace the current V1 shims in [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) with bridge-backed definitions
4. Re-express [`Coh.V1.CohMor`](../Coh/V1/Coh.lean:66) in terms of [`Coh.V2.CertifiedMor`](../Coh/V2/Certified.lean:14)
5. Update manuscript text so V2 is explicitly introduced as the projection-aware completion of V1 rather than a separate reboot

## Implementation order

1. Stabilize [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38)
2. Define the V1-to-V2 observable and hidden interpretation in [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean)
3. Build a V2 [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:16) instance from V1 semantics or from V1-level axioms explicitly marked as imported assumptions
4. Replace V1 morphism operations with wrappers around [`Coh.V2.idMor`](../Coh/V2/Certified.lean:42) and [`Coh.V2.compose`](../Coh/V2/Certified.lean:65)
5. Recompile V1 and V2 together to confirm the dependency direction is coherent

## Deliverables

- A bridge module connecting V1 operational semantics to V2 abstract semantics
- A cleaned V1 morphism API backed by V2 certification machinery
- A manuscript bridge section stating that V2 is the projection-aware categorical completion of V1
