# Reusable nonstandard analysis and transfer tools

The complete Jordan proof was saved first, at
[`first-complete-proof`](https://github.com/alok/JordanCurveTheorem/tree/first-complete-proof).
That checkpoint passed Comparator against the original full challenge, Nanoda, the
axiom audit, and fresh Lean kernel replay. The interface and metaprogramming changes
described here follow that checkpoint.

Import the generic library without the polygon development:

```lean
import Reeken.Nonstandard
```

This module imports no `Reeken.Geometry` or vendored `Schoenflies` modules. The
implementations use mathlib's `Filter.Germ`; they do not postulate transfer,
saturation, or standard parts.

## Internal objects

| Object | Representation | Main operations |
| --- | --- | --- |
| `Star U α` | Quotient of indexed families modulo `U` | `std`, `map`, internal application `app`, `pair`, `prodEquiv` |
| `InternalSet U α` | `Star U (Set α)` | Internal membership, `toSet`, `compl`, infimum, supremum, `image`, `prod` |
| `starDist x y` | Internal real obtained by extending `dist` | `near_iff_starDist`, distance of pairs, mapped distances |
| `Hyperfinite U α` | `Star U (Finset α)` | `toInternalSet`, `exists_max`, `exists_min` |
| `monad a` | Internal points infinitely close to standard `a` | `Near` and compact standard parts |
| `s.shadow` | Standard parts of internal points in `s` | Saturation through standard balls |
| `s.deep` | Standard points whose entire monad belongs to `s` | Compact inclusion and monotonicity |

Internal sets and functions are quotient objects, so their public operations do not
depend on a selected family. For example, `InternalSet.coe_image` gives
`(s.image f).toSet = app f '' s.toSet` for an arbitrary internal function `f`.
`InternalSet.toSet_injective` proves that internal sets are determined by their
internal elements, under its explicit nonempty-type hypothesis.

`InternalSet.countable_saturation` takes a sequence of internal sets and their finite
intersection property. It applies to **any** ultrafilter on the naturals containing
all tails. `InternalSet.mem_shadow_iff_internal_ball` uses this theorem to realize
all positive standard ball constraints with one internal point. The geometric model
instantiates these results with mathlib's chosen `hyperfilter ℕ`.

`InternalSet.mem_deep_iff` states the monad inclusion directly. Its compactness
consequence, `InternalSet.starSet_subset_of_isCompact`, has the whole NSA proof in
three steps: take an internal point of the compact set, take its standard part, and
use the standard part's monad inclusion. `CompactDeep.lean` now derives its finite
representative statement from this theorem. It no longer uses an auxiliary uniform
positive-distance argument.

The indexed `internalSet`, `hyperfiniteSet`, `shadow`, and `deep` interfaces remain
available at finite geometric construction boundaries. Their implementations or
bridge theorems use the internal-object API.

## Products and infinitesimal proximity

[`Products.lean`](../Reeken/Nonstandard/Products.lean) proves
`Star U (α × β) ≃ Star U α × Star U β`. `exists_pair` decomposes an internal
pair directly into internal coordinates; it does not expose representative families.
Internal Cartesian products have componentwise membership.
[`Hypermetric.lean`](../Reeken/Nonstandard/Hypermetric.lean) proves that `Near`
on pairs is equivalent to `Near` on both coordinates and that shadows commute
with internal Cartesian products. These results require no saturation hypothesis.
`starDist` takes values in the internal reals; the construction does not impose an
ordinary real-valued metric on the ultrapower.

[`Proximity.lean`](../Reeken/Nonstandard/Proximity.lean) provides
`InternalSet.exists_near_iff`: for two internal functions on an internal set,
arbitrarily small distances at every positive standard scale imply that **one**
internal argument makes their values infinitely close. The proof takes the internal
image of their distance function and applies the existing shadow theorem at zero.
For example:

```lean
open Filter Reeken.NSA in
example {α E : Type*} [Nonempty α] [PseudoMetricSpace E] {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ atTop) (s : InternalSet U α)
    (f g : Star U (α → E))
    (h : ∀ ε : ℝ, 0 < ε → ∃ x ∈ s, starDist (app f x) (app g x) < std ε) :
    ∃ x ∈ s, Near (app f x) (app g x) :=
  (InternalSet.exists_near_iff hU s f g).mpr h
```

The dual `InternalSet.not_exists_near_iff` gives one positive standard lower bound
when no internal argument makes the values infinitely close. Both lemmas require
the explicitly stated free-ultrafilter hypothesis on ℕ.

The Section 3 proof in
[`CompactSeparation.lean`](../Reeken/Nonstandard/CompactSeparation.lean) uses this
principle on an internal product, then takes a compact standard part. Its native
theorem works over any free ultrafilter on ℕ, and its proof contains no representative
extraction or eventual statements. The original indexed theorem is an adapter;
`star_transfer at h` translates the uniform internal inequality to the finite
geometric interface. The previous bespoke saturation construction is gone.

## Checked metaprogramming

`star_cases x y` chooses representatives for the listed internal objects and
substitutes into dependent hypotheses and the goal. It retains the names `x` and
`y` for the resulting families. Its private equality names are hygienic. Repeated
representative extraction throughout the NSA proof now uses this tactic.

`star_transfer`, optionally followed by a location such as `at h` or `at h₀ h₁ ⊢`,
normalizes the registered internal rules. The `star_transfer` simp set:

- evaluates standard embeddings, internal application, mapped predicates, and
  representative equality and order;
- normalizes internal pairs, product membership, mapped distances, maxima, and
  inequalities against standard bounds;
- collects Boolean combinations into internal predicates;
- transfers existential and universal quantifiers **over the full ultrapower**;
- translates internal set operations through their proved interpretation lemmas.

For example, this is a checked regression case:

```lean
example {ι α : Type*} {U : Ultrafilter ι} [Nonempty α]
    (P Q : ι → α → Prop) :
    (∃ x : Reeken.NSA.Star U α,
      Reeken.NSA.Holds P x ∧ ¬ Reeken.NSA.Holds Q x) ↔
      ∀ᶠ i in U, ∃ a, P i a ∧ ¬ Q i a := by
  star_transfer
```

The production `internal_induction` proof uses `star_transfer at hzero hstep ⊢`,
followed by ordinary natural-number induction. The macro and elaborator produce
ordinary proof terms; they add no oracle or axiom.

This is normalization for the explicit internal interface, not automatic
first-order reification of arbitrary Lean syntax. Additional proved rewrite rules
can be registered with `@[star_transfer]`. The attribute has its own orientation:
ordinary `simp` exposes Boolean structure, while transfer collects it before moving
internal quantifiers. Do not indiscriminately combine the two simp sets.

External predicates stay external. `Near`, `Unlimited`, and quantification over
standard points are not moved through the ultrafilter. The library proves
`standard_naturals_external` using overspill. Regression tests additionally check
that standard quantifiers retain their position and that `Near` is left untouched.

## Checking and possible upstream extraction

```sh
lake --wfail build Reeken.Nonstandard Verification.TransferTests
python3 scripts/check-solutions.py
lake env lean scripts/Audit.lean
lake env leanchecker --fresh Reeken
```

[`Verification/TransferTests.lean`](../Verification/TransferTests.lean) also checks
predicate substitution, Boolean formulas under internal quantifiers, dependent
hypotheses, and caller names that coincide with private tactic names. CI runs these
tests and every unchanged independent Comparator challenge after the refactor.
Product tests combine membership, independent coordinates, and negated predicates
under an internal quantifier. Metric tests check that the standard scale quantifier
stays outside the ultrafilter while internal witnesses move through it.

Potential mathlib submissions can be separated into three mathematical layers:
generic ultrapower/internal-set transfer over arbitrary ultrafilters; hyperfinite
extrema and countable saturation over free natural-number ultrafilters; and metric
monads, standard parts, and compact deep inclusion. The tactic and its rule set are
a fourth, separate tooling component. These are candidate extraction boundaries,
not submitted or accepted mathlib contributions. Upstream work should first reconcile
names and instances with existing `Filter.Germ` APIs and minimize imports. None of
these components needs the finite polygon library or the Jordan theorem.
