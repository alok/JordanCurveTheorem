import Lake
open Lake DSL

require JordanCurveTheorem from ".."
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "df72b022e558978a1c50264cfc4d7fec86fa8e04"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "4943d3335ffa9221a39949e60836a8ad5dc2a456"

package ReekenBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib ReekenBlueprint
