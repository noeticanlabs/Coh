import Coh.V1.Coh
import Coh.V2.Primitive
import Coh.V2.Definitions
import Coh.V2.Axioms

/- Smoke test: if this compiles, core is sorry-free -/

-- V1 basic types
#check Coh.V1.Trace
#check Coh.V1.Step
#check Coh.V1.concat

-- V2 core types
#check Coh.V2.System
#check Coh.V2.Fiber
#check Coh.V2.Assumptions

-- V2 certified types
#check Coh.V2.CertifiedMor

/- If this compiles, core is sorry-free -/
