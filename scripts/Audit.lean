import Reeken
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Reject any nonstandard axiom in every project declaration, including private helpers. -/
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    let source := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if (`Reeken).isPrefixOf source || (`Schoenflies).isPrefixOf source then
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax ↦ !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "{name} depends on forbidden axioms: {unexpected}"
      checked := checked + 1
  if checked == 0 then throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed for {checked} declarations defined in Reeken and Schoenflies modules (all namespaces)."
