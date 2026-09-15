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

-- Predicate substitution also works for a function varying with the ultrafilter index.
example (P : ι → β → Prop) (f : ι → α → β) :
    (∀ x : Star U α, Holds P (app (ofSeq f) x)) ↔
      ∀ᶠ i in U, ∀ a, P i (f i a) := by
  star_transfer

example (P Q : ι → α → Prop)
    (h : ∀ x : Star U α, Holds P x ∨ Holds Q x) :
    ∀ᶠ i in U, ∀ a, P i a ∨ Q i a := by
  star_transfer at h
  exact h

-- Internal membership must join the same predicate before moving a quantifier.
example (s : ι → Set α) (P : ι → α → Prop) :
    (∀ x : Star U α, x ∈ (ofSeq s : InternalSet U α) → Holds P x) ↔
      ∀ᶠ i in U, ∀ a ∈ s i, P i a := by
  star_transfer

-- Quantification over internal pairs includes both independent nonstandard coordinates.
example [Nonempty β] (s : ι → Set α) (t : ι → Set β)
    (P : ι → α → Prop) (Q : ι → β → Prop) :
    (∃ w : Star U (α × β), w ∈ InternalSet.prod (ofSeq s) (ofSeq t) ∧
      Holds P (map Prod.fst w) ∧ ¬ Holds Q (map Prod.snd w)) ↔
      ∀ᶠ i in U, ∃ w : α × β,
        (w.1 ∈ s i ∧ w.2 ∈ t i) ∧ P i w.1 ∧ ¬ Q i w.2 := by
  star_transfer

-- Product projections normalize while the external Near predicate stays in place.
example [PseudoMetricSpace α] (x y : Star U α) :
    Near (map Prod.fst (pair x y)) (map Prod.snd (pair x y)) ↔ Near x y := by
  star_transfer

-- This combines internal membership, mapped distances, max, and a standard bound.
-- It is the normalization used by the compact-separation adapter.
example [PseudoMetricSpace β] (s : ι → Set α) (f g h : α → β) (δ : ℝ) :
    (∀ x : Star U α, x ∈ (ofSeq s : InternalSet U α) →
      std δ ≤ max (starDist (map f x) (map h x)) (starDist (map g x) (map h x))) ↔
      ∀ᶠ i in U, ∀ a ∈ s i, δ ≤ max (dist (f a) (h a)) (dist (g a) (h a)) := by
  star_transfer

-- Standard scales must remain outside transfer, even around bounded quantifiers.
example [PseudoMetricSpace β] (s : ι → Set α) (f g : α → β) :
    (∀ ε : ℝ, 0 < ε → ∃ x : Star U α,
      x ∈ (ofSeq s : InternalSet U α) ∧
        starDist (map f x) (map g x) < std ε) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, ∃ a ∈ s i, dist (f a) (g a) < ε := by
  star_transfer

-- Ball inclusion transfers with both its center and radius varying internally.
example [PseudoMetricSpace α] (s : ι → Set α) (a : ι → α) (r : ι → ℝ) :
    (∀ x : Star U α, x ∈ InternalSet.ball (ofSeq a) (ofSeq r) →
      x ∈ (ofSeq s : InternalSet U α)) ↔
      ∀ᶠ i in U, ∀ x, dist x (a i) < r i → x ∈ s i := by
  star_transfer

-- The center can be nonstandard; a standard scale must stay outside the ultrafilter.
example [PseudoMetricSpace α] (s : ι → Set α) (a : ι → α) :
    (∀ ε : ℝ, 0 < ε → ∀ x : Star U α, x ∈ (ofSeq s : InternalSet U α) →
      starDist x (ofSeq a) < std ε) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, ∀ x ∈ s i, dist x (a i) < ε := by
  star_transfer

-- Deep membership is external, like Near, and must not be unfolded by transfer.
example [PseudoMetricSpace α] (s : InternalSet U α) (x : Star U α)
    (h : s.IsDeep x) : s.IsDeep x := by
  fail_if_success star_transfer
  guard_target =ₛ s.IsDeep x
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
