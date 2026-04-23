import Lake
open Lake DSL

package «Coh» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Coh» where
  srcDir := "."
  roots := #[
    `Coh.V1.Coh,
    `Coh.V2.Primitive,
    `Coh.V2.Definitions,
    `Coh.V2.Axioms,
    `Coh.V2.Analytic,
    `Coh.V2.Certified,
    `Coh.V2.Category,
    `Coh.V2.FiniteWord,
    `Coh.V2.BridgeLemmas,
    `Coh.V2.FromV1,
    `Coh.V2.FromV1Quotient
  ]
