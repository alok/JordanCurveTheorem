import Reeken.Nonstandard.Ultrapower
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Basic

/-!
# Proof-producing ultrapower normalization

`star_cases x y` replaces internal objects by representatives, substituting in dependent
hypotheses as well as the goal. `star_transfer` normalizes the registered internal operations
and logical rules. Neither tactic transfers external predicates such as infinitesimal closeness
or moves a quantifier over standard objects through an ultrafilter.

The extensible simp set is deliberately separate from the ambient simplifier. Every rewrite
is a proved theorem; the tactics produce ordinary kernel-checked proof terms.
-/

open Lean Elab Tactic Parser.Tactic

/-- Normalization rules for the proved internal transfer interface. -/
register_simp_attr star_transfer

/-- Choose representatives for the listed internal objects, retaining their names. -/
elab "star_cases" xs:(ppSpace colGt ident)+ : tactic => do
  for x in xs do
    evalTactic (← `(tactic|
      obtain ⟨$x, h⟩ := Reeken.NSA.ofSeq_surjective $x; cases h))

/-- Normalize registered internal operations and quantifiers at the goal or a location. -/
macro "star_transfer" loc:(location)? : tactic =>
  `(tactic| simp only [star_transfer] $[$loc]?)
