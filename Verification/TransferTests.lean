import Reeken.Nonstandard

/-!
# Transfer regression tests

Exercise Boolean combinations under internal quantifiers, predicate substitution,
dependent hypotheses, and the boundary between standard and internal quantification.
The geometric theorem is the integration test; these examples diagnose tactic regressions.
-/

open Filter Reeken.NSA

-- The reusable import must stay independent of the result it was developed to prove.
open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if (`Reeken.Geometry).isPrefixOf name || (`Schoenflies).isPrefixOf name ||
        name == `Reeken.Jordan then
      throwError "The generic NSA library imports geometry: {name}"

section Generic
variable {ι α β : Type*} {U : Ultrafilter ι} [Nonempty α]

example (P Q : ι → α → Prop) :
    (∃ x : Star U α, Holds P x ∧ ¬ Holds Q x) ↔
      ∀ᶠ i in U, ∃ a, P i a ∧ ¬ Q i a := by
  star_transfer

example (P : ι → β → Prop) (Q : ι → α → Prop) (f : α → β) :
    (∀ x : Star U α, Holds P (map f x) → Holds Q x) ↔
      ∀ᶠ i in U, ∀ a, P i (f a) → Q i a := by
  star_transfer

example (P Q : ι → α → Prop)
    (h : ∀ x : Star U α, Holds P x ∨ Holds Q x) :
    ∀ᶠ i in U, ∀ a, P i a ∨ Q i a := by
  star_transfer at h
  exact h

-- Substitution must reach a predicate depending on the original quotient object.
example (x : Star U α) (P : Star U α → Prop) (h : P x) :
    ∃ f : ι → α, P (ofSeq f) ∧ x = ofSeq f := by
  star_cases x
  exact ⟨x, h, rfl⟩

-- Names from the caller can coincide with the tactic's private equation name.
example (h : Star U α) (x : Star U β) :
    ∃ f : ι → α, ∃ g : ι → β, h = ofSeq f ∧ x = ofSeq g := by
  star_cases h x
  exact ⟨h, x, rfl, rfl⟩

-- Standard quantification stays outside the ultrafilter.
example (P : ι → α → Prop) (h : ∀ a : α, Holds (U := U) P (std a)) :
    ∀ a : α, ∀ᶠ i in U, P i a := by
  star_transfer at h
  guard_hyp h : ∀ a : α, ∀ᶠ i in U, P i a
  exact h

-- Infinitesimal closeness is external and is not unfolded by transfer normalization.
example [PseudoMetricSpace α] (x y : Star U α) (h : Near x y) : Near x y := by
  fail_if_success star_transfer
  guard_target =ₛ Near x y
  exact h

end Generic

-- A proved counterexample to treating the standard naturals as an internal set.
example : ¬ ∃ s : InternalSet (hyperfilter ℕ) ℕ,
    s.toSet = Set.range (std : ℕ → Hypernat) :=
  standard_naturals_external
