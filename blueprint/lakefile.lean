import Lake
open Lake DSL

require JordanCurveTheorem from ".."
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "9c5538fa3a83ff363c4f21ae4e5eafa1870f5e17"

package ReekenBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib ReekenBlueprint
