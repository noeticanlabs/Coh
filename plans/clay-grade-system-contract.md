# Coh Foundational Proof System Contract

## AMS integration note

This contract now combines two distinct standards:

1. a **foundational proof-system standard** appropriate for a high-rigor, problem-level mathematical program
2. an **AMS-style journal standard** appropriate for submission to a serious mathematical venue

The AMS does not publish a single official checklist for machine-verified foundational systems comparable to a Clay problem acceptance rule.

So this document does **not** claim to quote any official AMS proof-verification law.

Instead, it incorporates the kinds of standards AMS journals are known to enforce in practice:

- precise definitions
- correct and attributable theorem statements
- transparent hypotheses
- reproducible references and notation
- readable exposition
- mathematically meaningful examples
- publishable manuscript discipline
- proper bibliography and attribution

In short, this is a **combined foundational plus AMS-publication contract**.

## Status note

This document does **not** claim to reproduce any official Clay Mathematics Institute publication checklist.

Instead, it records a **Clay-grade-style** standard for foundational mathematics and machine-checked formalization: the level of rigor, reproducibility, proof transparency, and model non-vacuity that a referee would expect for a serious foundational submission.

## Governing principle

The Coh system is acceptable only if the following four layers are simultaneously satisfied:

1. **mathematical soundness**
2. **formal proof soundness**
3. **model non-vacuity**
4. **reproducible build integrity**

Failure at any one layer blocks foundational acceptance.

For journal readiness, failure at any one of the exposition, attribution, manuscript-structure, or reproducibility layers blocks submission readiness even if the Lean code is mathematically correct.

---

## Standard A: explicit specification boundary

The abstract system boundary must be frozen and minimal.

Required artifact:

- [`Coh/V2/Axioms.lean`](../Coh/V2/Axioms.lean)

Required condition:

- every abstract assumption is named, isolated, and used intentionally
- no hidden semantic obligations may remain outside [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:24)
- downstream theorems must state exactly which assumptions they consume

Acceptance rule:

- no theorem in [`Coh/V2/Analytic.lean`](../Coh/V2/Analytic.lean), [`Coh/V2/Certified.lean`](../Coh/V2/Certified.lean), or [`Coh/V2/Category.lean`](../Coh/V2/Category.lean) may rely on unstated operational facts imported informally from V1

---

## Standard A-AMS: precise statement and notation discipline

The manuscript side must satisfy the baseline standards expected in a serious AMS-style submission.

Required artifacts:

- the manuscript source tree
- the theorem map in [`plans/manuscript-lean-alignment-analysis.md`](./manuscript-lean-alignment-analysis.md)

Required condition:

- every symbol is defined before first essential use
- all overloaded terms such as cost, defect, spend, witness, projection, and trace are disambiguated
- theorem statements in prose and theorem statements in Lean agree in hypothesis strength
- notational shifts between manuscript and Lean are documented explicitly

Acceptance rule:

- no section may rely on suggestive language where a precise definition is required
- no manuscript theorem may silently strengthen or weaken a Lean theorem

---

## Standard B: no proof gaps

The formal codebase must contain no placeholder proofs.

Required artifacts:

- the complete Lean tree under [`Coh/V1/`](../Coh/V1/)
- the complete Lean tree under [`Coh/V2/`](../Coh/V2/)
- CI in [`.github/workflows/lean-ci.yml`](../.github/workflows/lean-ci.yml)

Required condition:

- no `sorry`
- no `axiom` declarations except those intentionally represented as fields of [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:24)
- no commented-out theorem bodies used as substitutes for proofs

Acceptance rule:

- CI must fail if any placeholder proof appears anywhere in the trusted modules

---

## Standard B-AMS: attribution, provenance, and scope honesty

The project must distinguish clearly between:

- classical background mathematics
- new mathematical contributions
- engineering design choices in the formalization
- conjectural interpretation or philosophical motivation

Required condition:

- category-theoretic background must be cited where appropriate
- any thermodynamic or physical interpretation must be explicitly labeled as interpretation unless formalized as theorem
- claims of novelty must be separated from claims of mechanized verification
- no rhetoric may imply that machine verification proves more than the formal theorems actually state

Acceptance rule:

- the manuscript must cleanly separate theorem, interpretation, and speculation

---

## Standard C: non-vacuity by concrete model

The axioms must be shown realizable in at least one nontrivial model.

Required artifacts:

- [`Coh/V2/FiniteWord.lean`](../Coh/V2/FiniteWord.lean)
- [`tests/FiniteWordTests.lean`](../tests/FiniteWordTests.lean)

Required condition:

- the seven abstract assumptions in [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:24) must be instantiated by a concrete system
- the model must be nontrivial: more than a one-object witness and more than a purely degenerate identity structure
- the model must expose the actual hidden/observable split claimed by the manuscript

Acceptance rule:

- the finite-word model must compile on a clean clone
- the test file must build under CI
- the model must witness genuine projection behavior, not merely restate the abstract definitions

---

## Standard C-AMS: meaningful examples and explanatory adequacy

For AMS-level readability, the framework must contain at least one example that is not only formally valid but mathematically explanatory.

Required artifacts:

- [`Coh/V2/FiniteWord.lean`](../Coh/V2/FiniteWord.lean)
- [`tests/FiniteWordTests.lean`](../tests/FiniteWordTests.lean)

Required condition:

- the example must illustrate why the axioms were chosen
- the example must be discussed in the manuscript as more than a vacuity witness
- the example must clarify the difference between hidden and observable cost structures

Acceptance rule:

- a referee should be able to learn the intended semantics of the framework from the example, not merely confirm consistency

---

## Standard D: bridge obligations are theorem-level obligations

The V1 to V2 bridge must prove that the operational kernel satisfies the V2 interface.

Required artifact:

- [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean)

Required theorem:

- [`assumptionsFromV1`](../Coh/V2/FromV1.lean:171)

Required condition:

- the bridge must discharge all fields of [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:24)
- no field may be filled by appeal to informal manuscript reasoning alone
- the bridge must make explicit where each proof comes from in V1 semantics

Acceptance rule:

- the bridge is not considered complete unless all observable laws, hidden-cost laws, fiber laws, and decomposition laws are explicitly packaged in [`assumptionsFromV1`](../Coh/V2/FromV1.lean:171)

---

## Standard D-AMS: manuscript theorem architecture

The paper must present the mathematics in an order recognizable to a journal referee:

1. primitives
2. definitions
3. assumptions
4. analytic lemmas
5. structural theorem
6. examples and consequences

Required condition:

- manuscript order should mirror the actual dependency graph in Lean
- no theorem should appear in the paper before its prerequisites are available formally
- major theorems should have proof sketches that reflect the true Lean proof route

Acceptance rule:

- the exposition must be referee-auditable without requiring the referee to infer the argument order themselves

---

## Standard E: theorem traceability

Each major manuscript claim must correspond to a named Lean theorem or structure.

Required artifacts:

- [`plans/manuscript-lean-alignment-analysis.md`](./manuscript-lean-alignment-analysis.md)
- [`plans/from-v1-module-contract.md`](./from-v1-module-contract.md)

Required condition:

- manuscript definitions map to Lean definitions
- manuscript propositions map to Lean theorems
- notation drift must be documented explicitly

Minimum theorem map:

- envelope soundness ↔ [`envelope_soundness`](../Coh/V2/Analytic.lean)
- envelope minimality ↔ [`envelope_minimality`](../Coh/V2/Analytic.lean)
- identity envelope ↔ [`delta_id`](../Coh/V2/Analytic.lean)
- subadditivity ↔ [`delta_subadd`](../Coh/V2/Analytic.lean)
- certified composition ↔ [`compose_certified`](../Coh/V2/Certified.lean)
- categorical closure ↔ [`certified_category`](../Coh/V2/Category.lean)

Acceptance rule:

- no major theorem may appear in the manuscript without a corresponding Lean target or a stated reason that it is expository only

---

## Standard E-AMS: bibliography and citation integrity

The manuscript must satisfy normal mathematical publication expectations for references.

Required condition:

- category theory background is properly cited
- proof assistant / Lean references are cited if the formalization is part of the contribution
- any analogy to thermodynamics, coarse-graining, or free energy is supported by literature or explicitly marked heuristic
- theorem names in the manuscript are internally cross-referenced consistently

Acceptance rule:

- no major conceptual dependency may appear without attribution or explicit declaration that it is introduced here as a new formal definition

---

## Standard F: dependency hygiene

The dependency graph must respect abstraction boundaries.

Required condition:

- [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) must remain abstract
- [`Coh/V2/FromV1.lean`](../Coh/V2/FromV1.lean) is the interpretation layer
- analytic and categorical modules must depend on the abstract interface, not on ad hoc V1 internals

Acceptance rule:

- no reverse dependency from [`Coh/V2/Primitive.lean`](../Coh/V2/Primitive.lean) into V1
- no bridge-specific hacks inside the generic analytic layer

---

## Standard F-AMS: definitions must be mathematically economical

An AMS-level referee will typically object if the formal layer contains unnecessary definitional bulk with no explanatory gain.

Required condition:

- each structure field in [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:24) must have a clear mathematical role
- no definition should exist solely because it made one local proof easier if it obscures the actual mathematics
- bridge-local helper constructions should not be mistaken for new mathematical primitives

Acceptance rule:

- the code and paper should exhibit minimality of core abstractions, not only correctness

---

## Standard G: reproducible build discipline

The system must build from a clean checkout without editor state, local cache assumptions, or manual patching.

Required artifacts:

- [`lean-toolchain`](../lean-toolchain)
- [`lakefile.lean`](../lakefile.lean)
- [`.github/workflows/lean-ci.yml`](../.github/workflows/lean-ci.yml)

Required condition:

- CI must run `lake build`
- CI must build the finite-word model explicitly
- CI must build the smoke test file and regression tests
- CI must fail hard on any compile failure

Acceptance rule:

- “works in editor” is not accepted as evidence
- only clean CI success counts as build certification

---

## Standard G-AMS: submission reproducibility package

For journal-quality submission, reproducibility should extend beyond Lean compilation.

Required artifacts:

- [`.github/workflows/lean-ci.yml`](../.github/workflows/lean-ci.yml)
- manuscript source tree
- precise toolchain information in [`lean-toolchain`](../lean-toolchain)

Required condition:

- a referee or editor should be able to identify the exact Lean version
- the manuscript version and formalization version should be synchronized
- build instructions should be short and explicit

Acceptance rule:

- the submission should function as a reproducible mathematical artifact, not only as a local development snapshot

---

## Standard H: independent witness models

At least two kinds of witnesses should exist in the ecosystem:

1. **bridge-instantiated witness model** from V1 via [`assumptionsFromV1`](../Coh/V2/FromV1.lean:171)
2. **standalone mathematical witness model** such as [`Coh/V2/FiniteWord.lean`](../Coh/V2/FiniteWord.lean)

Reason:

- the bridge proves compatibility with the operational kernel
- the standalone model proves the abstract axioms are mathematically inhabited independently of V1 engineering choices

Acceptance rule:

- foundational confidence is materially stronger if both models compile and expose the same abstract interface

---

## Standard H-AMS: significance and scope control

The manuscript must make a disciplined claim about what the framework establishes.

Required condition:

- if the result is a framework theorem, it should be presented as a framework theorem
- if the result is an application template, it should be presented as an application template
- if physical interpretation is offered, it must not be mistaken for a proved physical law

Acceptance rule:

- no claim of universality, physical inevitability, or problem-solving scope may exceed what is actually formalized in Lean

---

## Standard I: proof readability and referee auditability

The proof system must not only be correct but auditable.

Required condition:

- core theorem names are semantically meaningful
- module names reflect mathematical role
- theorem statements are short enough to inspect
- helper lemmas do not obscure the main proof route

Acceptance rule:

- a referee should be able to move from [`Coh/V2/Axioms.lean`](../Coh/V2/Axioms.lean) to [`Coh/V2/Analytic.lean`](../Coh/V2/Analytic.lean) to [`Coh/V2/Certified.lean`](../Coh/V2/Certified.lean) to [`Coh/V2/Category.lean`](../Coh/V2/Category.lean) and recover the entire mathematical story without reverse-engineering the codebase

---

## Standard I-AMS: exposition quality and referee usability

Even a formally correct system can fail journal review if the exposition is opaque.

Required condition:

- proofs in the manuscript must explain the strategic route, not just the endpoint
- the role of the hidden/observable split must be motivated before the main theorem depends on it
- examples, remarks, and diagrams should reduce conceptual burden rather than add terminology

Acceptance rule:

- a referee should be able to explain the main theorem after one careful reading of the manuscript and one pass through the module spine

---

## Standard J: semantic contract for acceptance

The system is declared foundationally acceptable only if all of the following are true:

- [`Coh.V2.Assumptions`](../Coh/V2/Axioms.lean:24) is complete and minimal
- [`assumptionsFromV1`](../Coh/V2/FromV1.lean:171) compiles and discharges the bridge obligations
- [`Coh/V2/FiniteWord.lean`](../Coh/V2/FiniteWord.lean) compiles and yields a nontrivial model
- [`.github/workflows/lean-ci.yml`](../.github/workflows/lean-ci.yml) enforces a clean build
- [`tests/FiniteWordTests.lean`](../tests/FiniteWordTests.lean) runs as a regression witness
- no placeholder proofs remain in the trusted core
- manuscript claims are aligned with the theorem map in [`plans/manuscript-lean-alignment-analysis.md`](./manuscript-lean-alignment-analysis.md)

If any one of these fails, the system is research-promising but not yet hardened to foundational publication standard.

---

## Standard J-AMS: combined submission contract

The project is journal-ready only if both tracks are satisfied:

### Formal track

- the code compiles cleanly
- the abstract assumptions are explicit
- the bridge is proven
- the non-vacuity witness compiles
- CI is reproducible

### Expository track

- the manuscript has precise definitions
- the theorem ordering mirrors the proof dependency graph
- all conceptual imports are cited or explicitly declared novel
- examples are mathematically explanatory
- theorem-to-code correspondence is frozen and auditable

If the formal track succeeds but the expository track fails, the project is mathematically strong but not yet submission-ready.

If the expository track succeeds but the formal track fails, the project is publishable only as an informal theory, not as a hardened mechanized contribution.

---

## Immediate enforcement checklist

- [ ] CI fails on any placeholder proof or compile break
- [ ] [`Coh/V2/FiniteWord.lean`](../Coh/V2/FiniteWord.lean) is part of the build target set
- [ ] [`tests/FiniteWordTests.lean`](../tests/FiniteWordTests.lean) is executed in CI
- [ ] [`assumptionsFromV1`](../Coh/V2/FromV1.lean:171) is explicitly cited in the manuscript as the bridge-certification theorem
- [ ] the finite-word model is cited in the manuscript as the non-vacuity witness
- [ ] the code/manuscript theorem map is frozen before submission
- [ ] the manuscript defines all symbols before use
- [ ] physical interpretation is explicitly separated from proved mathematics
- [ ] bibliography covers category background, Lean/formalization background, and any external interpretive framework relied on in exposition
- [ ] build instructions and toolchain information are included in the submission package

---

## Final contract statement

The Coh project shall be presented as a foundational proof system only if it satisfies this contract at the levels of abstract specification, bridge verification, concrete model existence, and reproducible build integrity.

Anything weaker may still be mathematically interesting, but it should be described as an advancing formal research program rather than a hardened foundational artifact.

When submitted in an AMS-style venue, it must additionally satisfy the standards of definitional precision, theorem traceability, exposition quality, citation integrity, and reproducible artifact packaging recorded above.
