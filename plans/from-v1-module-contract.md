# Contract for [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean)

## Purpose

[`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean) is the instantiation layer that turns the operational semantics in [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean) into a V2-compatible abstract system.

It should **not** redefine the V2 kernel from [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean). Instead, it should construct a concrete instance of [`Coh.V2.System`](../Coh/V2/Primitive.lean:20) from V1 data.

## Imports

[`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean) should import:

- [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean)
- [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean)
- optionally [`Coh/V2/Definitions.lean`](../Coh/V2/Definitions.lean) only if bridge-local lemmas immediately use fibers or delta

It should not force [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) to import V1.

## Namespace

Use a dedicated namespace such as:

- [`Coh.V2.FromV1`](../Coh/V2/FromV1.lean)

This makes it explicit that the file is an interpretation layer rather than a new foundational theory.

## Required inputs

The file should take or derive the following V1-side ingredients from [`Coh/V1/Coh.lean`](../Coh/V1/Coh.lean):

- V1 state space from the type parameter used by [`Coh.V1.Step`](../Coh/V1/Coh.lean:29), [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38), and [`Coh.V1.CohMor`](../Coh/V1/Coh.lean:66)
- visible traces from [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38)
- verifier acceptance from [`Coh.V1.RVAccept`](../Coh/V1/Coh.lean:56)
- operational spend from [`Coh.V1.traceSpend`](../Coh/V1/Coh.lean:42)
- operational defect from [`Coh.V1.traceDefect`](../Coh/V1/Coh.lean:49)
- identity and composition primitives from [`Coh.V1.emptyTrace`](../Coh/V1/Coh.lean:58) and [`Coh.V1.concat`](../Coh/V1/Coh.lean:62)

## Definitions that must be exposed

### 1. Hidden witness carrier

Expose a hidden witness type representing verifier-realizing executions over a visible trace.

Suggested names:

- [`hiddenWitness`](../Coh/V2/FromV1.lean)
- [`V1Hidden`](../Coh/V2/FromV1.lean)

This object should package at least:

- a visible V1 trace
- a proof or certificate of acceptance under [`Coh.V1.RVAccept`](../Coh/V1/Coh.lean:56)
- hidden cost data if the hidden cost is not taken directly from V1 defect/spend summaries

### 2. Observable carrier

Expose the V1-derived observable carrier.

Suggested name:

- [`observableTrace`](../Coh/V2/FromV1.lean)

In the simplest version this is just [`Coh.V1.Trace`](../Coh/V1/Coh.lean:38), though a refined endpoint-indexed trace type may replace it later.

### 3. Hidden system

Expose a concrete [`Coh.V2.HiddenSystem`](../Coh/V2/Primitive.lean:8).

Suggested name:

- [`hiddenSystemFromV1`](../Coh/V2/FromV1.lean)

Required fields:

- hidden carrier
- partial composition of hidden witnesses
- hidden cost

### 4. Observable system

Expose a concrete [`Coh.V2.ObservableSystem`](../Coh/V2/Primitive.lean:14).

Suggested name:

- [`observableSystemFromV1`](../Coh/V2/FromV1.lean)

Required fields:

- carrier built from V1 traces
- observable composition induced by [`Coh.V1.concat`](../Coh/V1/Coh.lean:62)
- identity induced by [`Coh.V1.emptyTrace`](../Coh/V1/Coh.lean:58)

### 5. Projection

Expose the map from hidden witnesses to observable traces.

Suggested name:

- [`projFromV1`](../Coh/V2/FromV1.lean)

This is the concrete realization of the V2 projection in [`Coh.V2.System.proj`](../Coh/V2/Primitive.lean:23).

### 6. System package

Expose the complete instantiated system.

Suggested name:

- [`systemFromV1`](../Coh/V2/FromV1.lean)

Type:

- [`Coh.V2.System`](../Coh/V2/Primitive.lean:20)

## Theorems and lemmas that must be exposed

### Observable laws

The bridge should prove or postulate bridge-local lemmas showing that the V1-induced observable structure satisfies the V2 composition convention.

Suggested exports:

- [`obs_id_right_fromV1`](../Coh/V2/FromV1.lean)
- [`obs_id_left_fromV1`](../Coh/V2/FromV1.lean)
- [`obs_assoc_fromV1`](../Coh/V2/FromV1.lean)

These will feed [`Coh.V2.Assumptions.obs_id_right`](../Coh/V2/Axioms.lean:26), [`Coh.V2.Assumptions.obs_id_left`](../Coh/V2/Axioms.lean:30), and [`Coh.V2.Assumptions.obs_assoc`](../Coh/V2/Axioms.lean:18).

### Fiber / realizability laws

The bridge should prove or postulate that accepted V1 traces correspond to nonempty fibers.

Suggested exports:

- [`fiber_nonempty_fromV1`](../Coh/V2/FromV1.lean)
- [`id_fiber_zero_fromV1`](../Coh/V2/FromV1.lean)
- [`fiber_decomp_fromV1`](../Coh/V2/FromV1.lean)

These will feed the matching fields in [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:16).

### Hidden cost laws

The bridge should prove or postulate the hidden-cost additivity law induced by V1 operational composition.

Suggested export:

- [`hidden_cost_add_fromV1`](../Coh/V2/FromV1.lean)

### Assumptions package

Expose a full V2 assumptions instance.

Suggested name:

- [`assumptionsFromV1`](../Coh/V2/FromV1.lean)

Type:

- [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:16)

## Downstream API expected from the bridge

The rest of V2 should be able to consume the bridge through the following pattern:

- [`Coh.V2.delta`](../Coh/V2/Definitions.lean:21) applied to [`systemFromV1`](../Coh/V2/FromV1.lean)
- [`Coh.V2.CertifiedMor`](../Coh/V2/Certified.lean:14) instantiated with [`systemFromV1`](../Coh/V2/FromV1.lean) and [`assumptionsFromV1`](../Coh/V2/FromV1.lean)
- [`Coh.V2.certifiedCategory`](../Coh/V2/Category.lean:107) instantiated over the V1-derived system

## Non-goals

[`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean) should not:

- reprove the generic analytic theory from [`Coh/V2/Analytic.lean`](../Coh/V2/Analytic.lean)
- redefine [`Coh.V2.System`](../Coh/V2/Primitive.lean:20)
- replace V1 syntax with V2 syntax

Its role is interpretation, packaging, and transport.
