# The Jordan curve theorem, for humans

This page explains what this repository proves, why it is harder than it looks, how the
proof works, and why you can trust the result. It starts with pictures and ends with
the exact Lean statement. Stop reading wherever you have what you need.

**Reading paths**

| You have | Read |
| --- | --- |
| 2 minutes | [The theorem in one picture](#1-the-theorem-in-one-picture) and [the idea in one picture](#3-the-idea-in-one-picture) |
| 20 minutes | Everything on this page, top to bottom |
| 2 hours | This page, then the [proof roadmap](#4-the-proof-roadmap) files in order, the [source correspondence](source-map.md), and the [NSA tooling guide](nonstandard-tooling.md) |

Unfamiliar term? The [glossary](#glossary) at the end defines each one in a line.

---

## 1. The theorem in one picture

Draw a closed loop on paper without lifting the pen and without crossing your own line.
The loop cuts the page into exactly two pieces: a bounded **inside** and an unbounded
**outside**, and the loop is the edge of both.

![A simple closed curve with its inside shaded blue and its outside shaded yellow](figures/inside-outside.svg)

That is the Jordan curve theorem. This repository proves it in Lean 4 for **every**
continuous, non-self-intersecting loop in the plane. The proved statement also says
that the inside has no holes (it is *simply connected*): any loop drawn inside it can
be shrunk to a point without leaving it.

## 2. Why something so obvious is hard

"Continuous and non-self-intersecting" allows far stranger loops than anything you can
draw:

- The **Koch snowflake** is a Jordan curve with no tangent line at any point and
  infinite length. You cannot walk along it and "keep the inside on your left" in any
  naive sense.
- **Osgood** (1903) constructed Jordan curves of *positive area*: the curve itself,
  as a set of points, has positive area, even though it contains no disc, however
  small.

The theorem must cover all of these. Any proof that leans on smoothness, finite length,
or a picture fails. That is why the theorem is famous as an "obvious" result that
needs a genuinely careful proof.

For **polygons** the problem is much easier. To decide if a point is inside, shoot a
ray from it (one that misses the corners) and count how many edges it crosses. An odd
count means inside; an even count means outside.

![Ray-crossing parity: point A's ray crosses once, so A is inside; point B's ray crosses twice, so B is outside](figures/ray-parity.svg)

The strategy of the proof is to reduce the wild case to the polygon case.

## 3. The idea in one picture

Vladimir Kanovei and Michael Reeken's proof
([published paper](https://www.maths.ed.ac.uk/~v1ranick/jordan/jor.pdf), *Real Analysis
Exchange* 24(1), 161–170) uses **nonstandard analysis**, which provides genuine
infinitesimal numbers.

![Three panels: an arbitrary curve; an inscribed polygon with infinitesimally short edges; the standard inside and outside obtained from the polygon's regions](figures/nonstandard-idea.svg)

1. Start with an arbitrary continuous loop. Assume nothing else about it.
2. Inscribe a polygon whose vertices lie on the loop and whose edges are all
   **infinitesimally** short. Then clean it up so it does not cross itself. A
   non-self-intersecting polygon has an inside and an outside by the finite polygon
   theorem, which is hard to formalize but involves no limits.
3. Bring that picture back to the ordinary plane. An ordinary point is in the
   **standard inside** when every point infinitely close to it is inside the polygon,
   and likewise for the outside. The ordinary points infinitely close to some point of
   the polygon are exactly the points of the original loop: the polygon's *shadow* is
   the loop.

The set of all points infinitely close to a point is called its **monad**. Under a
microscope of infinite magnification, a point *deep inside* sees only the polygon's
inside. A point on the curve sees the polygon pass right through its monad, so it
belongs to neither region.

![Left: a curve with point a inside it and point b on it. Right: magnified monads. The monad of a lies entirely inside the polygon; the monad of b is cut by the polygon's zigzag edges](figures/deep-vs-curve.svg)

The remaining work, which is most of this repository, proves that these two standard
regions have every property the theorem promises: open, nonempty, path connected,
bounded or unbounded, with the loop as common boundary, and an inside with no holes.

## 4. The proof roadmap

Each box is one mathematical step. Arrows mean "is used by". The table below links the
Lean files for each step. The step names and files come from the
[README](../README.md) and the [source correspondence ledger](source-map.md).

```mermaid
flowchart TD
    A["Loop as a map from the circle"] --> D
    B["Nonstandard foundations: ultrapower, transfer, saturation, shadows"] --> C
    C["Lemma 1: inscribed polygon with infinitesimal edges"] --> D
    D["Lemma 2: make the polygon simple"] --> F
    E["Finite polygon Jordan theorem (vendored)"] --> F
    F["Standard inside and outside: open, disjoint, cover the complement"] --> G
    F --> H
    F --> I
    F --> K
    G["Inside bounded, outside unbounded"] --> Z
    H["Section 3: the curve is the common boundary"] --> Z
    I["Lemma 3: one inner polygon holds all inside points"] --> J
    I --> L
    J["Inside is path connected"] --> Z
    K["Outside is path connected (dual outer-polygon argument)"] --> Z
    M["Finite polygons contract: diagonals and ears"] --> L
    L["Inside is simply connected"] --> Z
    Z["Final theorem: Reeken.jordanCurveTheorem"]
```

| Step | Lean files |
| --- | --- |
| Loop as a map from the circle | [`CircleParametrization.lean`](../Reeken/Geometry/CircleParametrization.lean), [`SimpleLoop.lean`](../Reeken/Geometry/SimpleLoop.lean) |
| Nonstandard foundations | [`Ultrapower.lean`](../Reeken/Nonstandard/Ultrapower.lean), [`Hyperfinite.lean`](../Reeken/Nonstandard/Hyperfinite.lean), [`Saturation.lean`](../Reeken/Nonstandard/Saturation.lean), [`Metric.lean`](../Reeken/Nonstandard/Metric.lean), [`Shadow.lean`](../Reeken/Nonstandard/Shadow.lean) |
| Lemma 1: infinitesimal inscribed polygon | [`InitialPolygon.lean`](../Reeken/Nonstandard/InitialPolygon.lean), [`PolygonApproximation.lean`](../Reeken/Nonstandard/PolygonApproximation.lean), [`PolygonArcs.lean`](../Reeken/Nonstandard/PolygonArcs.lean) |
| Lemma 2: simple approximation | [`SimpleApproximation.lean`](../Reeken/Nonstandard/SimpleApproximation.lean) |
| Finite polygon Jordan theorem | [`PolygonSeparation.lean`](../Reeken/Geometry/PolygonSeparation.lean), [`vendor/`](../vendor/README.md) |
| Standard inside and outside | [`Regions.lean`](../Reeken/Nonstandard/Regions.lean), [`StandardRegions.lean`](../Reeken/Nonstandard/StandardRegions.lean) |
| Bounded inside, unbounded outside | [`ExteriorBounds.lean`](../Reeken/Geometry/ExteriorBounds.lean), [`RegionBounds.lean`](../Reeken/Nonstandard/RegionBounds.lean) |
| Section 3: common boundary | [`CommonBoundary.lean`](../Reeken/Nonstandard/CommonBoundary.lean) |
| Lemma 3: simultaneous containment | [`RingContainment.lean`](../Reeken/Nonstandard/RingContainment.lean) |
| Inside path connected | [`InsideConnectivity.lean`](../Reeken/Nonstandard/InsideConnectivity.lean) |
| Outside path connected (dual outer-polygon argument) | [`OuterContainment.lean`](../Reeken/Nonstandard/OuterContainment.lean), [`OutsideConnectivity.lean`](../Reeken/Nonstandard/OutsideConnectivity.lean) |
| Finite polygon contraction | [`PolygonDiagonal.lean`](../Reeken/Geometry/PolygonDiagonal.lean), [`PolygonEars.lean`](../Reeken/Geometry/PolygonEars.lean) |
| Inside simply connected | [`LoopContraction.lean`](../Reeken/Nonstandard/LoopContraction.lean), [`SimplyConnected.lean`](../Reeken/Nonstandard/SimplyConnected.lean) |
| Final theorem | [`Jordan.lean`](../Reeken/Jordan.lean) |

The [source correspondence ledger](source-map.md) has a row-by-row map at much finer
grain, about sixty steps.

## 5. Nonstandard analysis, gently

**What it is.** Nonstandard analysis enlarges the real numbers with infinitesimals (nonzero
numbers whose size is smaller than every ordinary positive real) and their reciprocals,
the unlimited numbers. It is fully rigorous; it is not a heuristic.

**How this repo builds it.** No new axioms are added. A "nonstandard" object is a
*sequence* of ordinary objects, and two sequences count as equal when they agree
"almost always", where an
[ultrafilter](https://en.wikipedia.org/wiki/Ultrafilter) decides what "almost always"
means. Mathlib already has this construction as `Filter.Germ`; the repository's
extension is just that:

```lean
/-- The extension of a type over the ultrafilter `U`. -/
abbrev Star (U : Ultrafilter ι) (α : Type v) := Germ (U : Filter ι) α
```

([`Ultrapower.lean`](../Reeken/Nonstandard/Ultrapower.lean)). An ordinary point `a` is
included as the constant sequence `std a`. For the final theorem the ultrafilter is
`hyperfilter ℕ`, a *free* ultrafilter on the natural numbers. Over it, the sequence
1, 1/2, 1/3, … names a positive infinitesimal, because for each fixed ε > 0 all but
finitely many terms are smaller than ε. "Infinitely close" is defined directly:

```lean
/-- Two internal points are close at every positive standard metric scale. -/
def Near [PseudoMetricSpace α] (x y : Star U α) : Prop :=
  ∀ ε : ℝ, 0 < ε → Germ.LiftRel (fun a b ↦ dist a b < ε) x y
```

([`Metric.lean`](../Reeken/Nonstandard/Metric.lean)). In words: for every ordinary
ε > 0, the two sequences are within ε of each other almost always.

**Monads, shadows, and deep points.** These three definitions turn the picture in
[section 3](#3-the-idea-in-one-picture) into Lean. They are quoted from
[`InternalMetric.lean`](../Reeken/Nonstandard/InternalMetric.lean):

```lean
/-- The monad of a standard point consists of all internal points infinitely close to it. -/
def monad (a : α) : Set (Star U α) := {x | Near x (std a)}

/-- The standard shadow of an internal set. This is generally an external set. -/
def shadow (s : InternalSet U α) : Set α := {a | ∃ x ∈ s.toSet, Near x (std a)}

/-- A standard point is deep in an internal set when its monad avoids the complement. -/
def deep (s : InternalSet U α) : Set α := s.compl.shadowᶜ
```

So `a` is deep in `s` when no point outside `s` is infinitely close to `a`. The same
file proves that this is the same as the whole monad lying in `s`
(`InternalSet.mem_deep_iff`, whose statement is
`a ∈ s.deep ↔ monad a ⊆ s.toSet`).

**The two regions.** In Lean the infinitesimal polygon is given by an ordinary sequence
`p : ℕ → InscribedPolygon f` of finer and finer polygons inscribed in the curve `f`. The
regions of the final theorem are the points deep inside, and deep outside, that
polygon:

```lean
def standardInside : Set Schoenflies.Plane := deep (fun i ↦ Schoenflies.inside (p i).trace)

def standardOutside : Set Schoenflies.Plane := deep (fun i ↦ Schoenflies.outside (p i).trace)
```

([`StandardRegions.lean`](../Reeken/Nonstandard/StandardRegions.lean)). Here `deep`
takes the sequence of ordinary sets `i ↦ inside (p i).trace` and applies the internal
`deep` above to the internal set it represents
([`Regions.lean`](../Reeken/Nonstandard/Regions.lean)). A point on the polygon itself
is in neither side, so `standardInside` excludes every point with a polygon point
infinitely close, and `standardOutside` does too.

**Why use it here.** A classical proof would approximate the curve by a sequence of
polygons and keep careful track of how errors shrink. With an infinitesimal polygon
there is one polygon whose edges are infinitely close to the curve, so many
epsilon-management steps become a single statement of the form "these are infinitely
close".

**How the finite polygon theorem is used.** The finite theorem is never applied to a
nonstandard object. It is applied to each ordinary polygon `p i`, for "almost every"
`i` in the ultrafilter's sense (written `∀ᶠ i in hyperfilter ℕ`):

```lean
theorem eventually_polygon_separates
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
    (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple) :
    ∀ᶠ i in hyperfilter ℕ, Schoenflies.IsSeparating (p i).trace := by
  filter_upwards [hs, vertex_count_unlimited p hmax 2] with i hi hn
  exact hi.isSeparating (by omega)
```

([`StandardRegions.lean`](../Reeken/Nonstandard/StandardRegions.lean)). The hypothesis
`hmax` says the edges are infinitesimal; `hs` says almost every `p i` is simple. The
proof uses the finite theorem (`hi.isSeparating`) on one ordinary polygon at a time.
That "almost every `i`" statement then *is*, by definition, a statement about the single
infinitesimal polygon. In
[`InternalSeparation.lean`](../Reeken/Nonstandard/InternalSeparation.lean) the two
sides are related by `Iff.rfl`:

```lean
@[simp, star_transfer] theorem separates_ofSeq (u v b : ι → Set E) :
    Separates (ofSeq (U := U) u) (ofSeq v) (ofSeq b) ↔
      ∀ᶠ i in U, IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧
        u i ∪ v i = (b i)ᶜ := Iff.rfl
```

This is **transfer** (Łoś's theorem) carried out for one specific statement. The
library does not prove a single metatheorem about all formulas. Instead it proves
transfer rule by rule, for the logical connectives and quantifiers in
[`Ultrapower.lean`](../Reeken/Nonstandard/Ultrapower.lean) and for each registered
operation, and the `star_transfer` tactic applies those rules.

### Reading a nonstandard statement in Lean

Here is one theorem, quoted from
[`Regions.lean`](../Reeken/Nonstandard/Regions.lean), that states the nonstandard
idea and its ordinary epsilon meaning side by side:

```lean
theorem mem_deep_iff (s : ℕ → Set E) (a : E) :
    a ∈ deep s ↔ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ i in hyperfilter ℕ, ∀ x ∉ s i, ε ≤ dist x a :=
  not_mem_shadow_iff _ _
```

- `s : ℕ → Set E` is a sequence of ordinary sets, for example the insides of the
  polygons `p i`. Together they represent one internal set.
- `a ∈ deep s` is the nonstandard side: every point infinitely close to `a` is in
  that internal set.
- The right side is ordinary analysis. There is one fixed positive distance `ε` such
  that, for almost every `i`, every point outside `s i` is at least `ε` away from `a`.
  In other words, `a` stays a definite distance from the edge of the region.
- The proof is one line because it reuses `not_mem_shadow_iff` from
  [`Shadow.lean`](../Reeken/Nonstandard/Shadow.lean). That proof uses *countable
  saturation*: if for every positive distance there were points outside `s i` that
  close to `a`, then a single nonstandard point *outside the internal set* would be
  infinitely close to `a`, so `a` would not be deep.

The transfer tactic is tested on small examples like this one, from
[`Verification/TransferTests.lean`](../Verification/TransferTests.lean):

```lean
-- Ball inclusion transfers with both its center and radius varying internally.
example [PseudoMetricSpace α] (s : ι → Set α) (a : ι → α) (r : ι → ℝ) :
    (∀ x : Star U α, x ∈ InternalSet.ball (ofSeq a) (ofSeq r) →
      x ∈ (ofSeq s : InternalSet U α)) ↔
      ∀ᶠ i in U, ∀ x, dist x (a i) < r i → x ∈ s i := by
  star_transfer
```

The left side quantifies over *all* internal points, including nonstandard ones. It
says that the internal ball with center `a` and radius `r` lies in the internal set
`s`. The right side says that, for almost every `i`, the ordinary ball of radius `r i`
around `a i` lies in `s i`. The tactic proves the equivalence with ordinary,
kernel-checked rewriting. The same file checks the boundaries of transfer too:
`Near` and deep membership are *external* notions, and the tactic must leave them
untouched.

## 6. The final statement, line by line

From [`Reeken/Jordan.lean`](../Reeken/Jordan.lean):

```lean
theorem jordanCurveTheorem
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      inside.Nonempty ∧ outside.Nonempty ∧
      IsOpen inside ∧ IsOpen outside ∧ Disjoint inside outside ∧
      inside ∪ outside = (Set.range r)ᶜ ∧
      IsPathConnected inside ∧ IsPathConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      frontier inside = Set.range r ∧ frontier outside = Set.range r ∧
      IsSimplyConnected inside := by
```

| Lean | Plain English |
| --- | --- |
| `r : Metric.sphere (0 : …) 1 → EuclideanSpace ℝ (Fin 2)` | `r` places each point of the unit circle in the plane; its image is the curve. |
| `hcont : Continuous r` | The curve is drawn without lifting the pen. |
| `hinj : Function.Injective r` | It never touches itself: different circle points go to different plane points. |
| `∃ inside outside : Set …` | There exist two sets of points in the plane, such that: |
| `inside.Nonempty ∧ outside.Nonempty` | both actually contain points; |
| `IsOpen inside ∧ IsOpen outside` | each point of either region has a small disc around it in the same region; |
| `Disjoint inside outside` | no point is in both; |
| `inside ∪ outside = (Set.range r)ᶜ` | together they are exactly the points *not* on the curve; |
| `IsPathConnected inside ∧ IsPathConnected outside` | each region is one piece: any two of its points are joined by a path inside it; |
| `Bornology.IsBounded inside` | the inside fits in some disc; |
| `¬ Bornology.IsBounded outside` | the outside does not; |
| `frontier inside = Set.range r ∧ frontier outside = Set.range r` | the boundary of each region is exactly the curve; |
| `IsSimplyConnected inside` | the inside has no holes: every loop in it shrinks to a point within it. |

The hypotheses mention only the curve. Nothing about polygons, separation, or
approximation is assumed.

## 7. How do we know it's right?

You do not have to trust the authors or read the proof. Here is what the repository
and its CI actually check.

1. **Lean's kernel checks every step.** The theorem compiles only if each inference
   is valid. Proof modules contain no `sorry` (an "I'll prove it later" placeholder),
   no added axioms, and no `native_decide`. The audit below would catch any of these,
   because each one shows up as an extra axiom.
2. **Axiom audit.** [`scripts/Audit.lean`](../scripts/Audit.lean) walks every
   declaration defined in the project and vendored modules, including private helpers,
   and fails unless each depends only on Lean's three standard axioms: `propext`,
   `Classical.choice`, and `Quot.sound`.
3. **Fresh kernel replay.** `lake env leanchecker --fresh Reeken` re-checks the entire
   imported environment from scratch.
4. **Independent statements, second kernel.** [`Verification/`](../Verification/)
   contains *challenge* files. Each states a result using only mathlib definitions, with
   no project definitions. The final
   [`JordanChallenge.lean`](../Verification/JordanChallenge.lean) has the same statement as
   above. A reader only needs to check that the challenge says the right thing.
   [Comparator](https://github.com/leanprover/comparator) checks that each solution
   proves the unchanged challenge with only the permitted axioms. It replays the proof
   in [**Nanoda**](https://github.com/robsimmons/nanoda_lib), an independent kernel
   implementation. Ten such targets cover the foundations, intermediate milestones, and
   the full theorem. The checker runs inside a
   [Landrun](https://github.com/zouuup/landrun) sandbox.
5. **Continuous integration.** Both run on every push:
   [Lean build, audit, and fresh replay](https://github.com/alok/JordanCurveTheorem/actions/workflows/lean.yml)
   and [Comparator and Nanoda](https://github.com/alok/JordanCurveTheorem/actions/workflows/comparator.yml).

To reproduce locally:

```sh
lake exe cache get
python3 scripts/check-solutions.py
lake env lean scripts/Audit.lean
lake env leanchecker --fresh Reeken
```

The Comparator and Nanoda check runs on Linux. The CI workflow builds the pinned
checkers with [`scripts/install-checkers.sh`](../scripts/install-checkers.sh).

## 8. What is proved, and where it differs from the paper

**Proved:** the full theorem above, for every continuous injective map of the circle
into the plane. The [source ledger](source-map.md) records the status of each step of
the paper's argument.

**Borrowed, with attribution.** The paper *assumes* the Jordan theorem for polygons.
This project proves it instead, using finite polygon modules vendored from
[Álvaro Begué's schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean)
(Apache 2.0). These modules are third-party proof code, not original project work.
Only the finite polygonal part is used; that project's general Jordan and Schoenflies
assembly is excluded. See
[`vendor/README.md`](../vendor/README.md).

**Where the formal proof takes a different route.** Each item is documented and
justified in the [source ledger](source-map.md):

- *Exterior connectivity.* The paper uses an inversion step. The formal proof instead
  reuses the infinitesimal-barrier argument on an outer polygon, the dual of the inside
  argument. It proves the same conclusion but does not formalize the inversion step.
- *Simultaneous containment (Lemma 3).* The formal proof uses finite crossing parity
  instead of classifying all ring domains.
- *Loop cutting (Lemma 2).* The paper's step-by-step removal of self-crossings becomes
  a choice of a polygon with the fewest vertices. Overlapping adjacent edges, which the
  arXiv version mentions, are excluded explicitly.
- *Simple connectivity.* The proof handles every continuous loop in the inside,
  including self-intersecting ones. Each loop lies inside one finite polygon whose
  closed inside stays in the curve's inside, and contracting that polygon contracts the
  loop.
- *Typos corrected.* The published condition (†) does not require the last vertex to
  lie on the curve, though later steps need it. Section 3 prints an equal-distance
  condition with a minus sign where equality is meant. In Lemma 3, a common-endpoint
  condition is printed for two vertices but must refer to their nearest points
  ("feet") on the boundary.

**Beyond the theorem.** The nonstandard machinery is packaged as a reusable library
(`import Reeken.Nonstandard`): internal sets, tactics for choosing representatives
(`star_cases`) and for transfer (`star_transfer`), saturation, and shadows. See the
[NSA tooling guide](nonstandard-tooling.md).

## Glossary

Each term has a one-line meaning and the file where it lives. Paths are relative to
[`Reeken/Nonstandard/`](../Reeken/Nonstandard/) unless stated otherwise.

| Term | Plain meaning | In the code |
| --- | --- | --- |
| Ultrafilter | A rule that decides, for every set of indices, whether it counts as "almost all". It fixes what "almost always" means for sequences. | Mathlib's `Ultrafilter`; the final theorem uses the free ultrafilter `hyperfilter ℕ`. |
| Nonstandard point, `Star U α` | A sequence of ordinary points, with two sequences identified when they agree almost always. | `Star`, `ofSeq` in [`Ultrapower.lean`](../Reeken/Nonstandard/Ultrapower.lean) |
| Standard point, `std a` | An ordinary point, viewed as the constant sequence. | `std` in [`Ultrapower.lean`](../Reeken/Nonstandard/Ultrapower.lean) |
| Infinitesimal | Smaller in absolute value than every ordinary positive number. Zero is one, but there are nonzero ones too. The code usually states this directly, e.g. edges with `∀ ε > 0, ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε`. | `hmax` hypotheses in [`StandardRegions.lean`](../Reeken/Nonstandard/StandardRegions.lean) |
| Infinitely close | Two points whose distance is infinitesimal. | `Near` in [`Metric.lean`](../Reeken/Nonstandard/Metric.lean) |
| Monad | All points infinitely close to a given ordinary point. | `monad` in [`InternalMetric.lean`](../Reeken/Nonstandard/InternalMetric.lean) |
| Standard part | An ordinary point infinitely close to a given nonstandard point. One exists when the nonstandard point lies in the extension of a compact set. | `compact_standard_part` in [`Metric.lean`](../Reeken/Nonstandard/Metric.lean) |
| Shadow | All ordinary points that are infinitely close to some point of a nonstandard set. | `InternalSet.shadow` in [`InternalMetric.lean`](../Reeken/Nonstandard/InternalMetric.lean); sequence form `shadow` in [`Shadow.lean`](../Reeken/Nonstandard/Shadow.lean) |
| Deep | An ordinary point is deep in a set when its whole monad lies in the set. | `InternalSet.deep` in [`InternalMetric.lean`](../Reeken/Nonstandard/InternalMetric.lean); `deep` in [`Regions.lean`](../Reeken/Nonstandard/Regions.lean) |
| Internal | Built from a sequence of ordinary objects, one per index, so that finite theorems can be applied index by index. Internal sets are the nonstandard sets transfer works on. | `Holds`, `internalSet` in [`Ultrapower.lean`](../Reeken/Nonstandard/Ultrapower.lean); `InternalSet` in [`InternalSet.lean`](../Reeken/Nonstandard/InternalSet.lean) |
| External | A notion that is not internal, such as "infinitely close", "monad", or "the standard naturals". Transfer does not apply to it. | `standard_naturals_external` in [`Saturation.lean`](../Reeken/Nonstandard/Saturation.lean) |
| Transfer | A statement about internal objects holds exactly when the corresponding ordinary statement holds for almost every index. | `exists_holds`, `forall_holds` in [`Ultrapower.lean`](../Reeken/Nonstandard/Ultrapower.lean); `star_transfer` in [`Transfer.lean`](../Reeken/Nonstandard/Transfer.lean) |
| Countable saturation | If countably many internal conditions can always be met finitely many at a time, one internal point meets them all. It turns "arbitrarily close" into "infinitely close". | [`Saturation.lean`](../Reeken/Nonstandard/Saturation.lean) |
| Simply connected | Path connected, and every loop can be shrunk to a point without leaving the set: no holes. | Mathlib's `IsSimplyConnected`; proved for the inside in [`SimplyConnected.lean`](../Reeken/Nonstandard/SimplyConnected.lean) |

## Where to go next

- [`README.md`](../README.md): build instructions and the module map.
- [`docs/source-map.md`](source-map.md): every paper step mapped to Lean files, with justified corrections.
- [`docs/nonstandard-tooling.md`](nonstandard-tooling.md): the reusable NSA library.
- [`blueprint/`](../blueprint/README.md): a Verso blueprint linking the mathematical steps to checked declarations.
- The original complete proof, before the NSA refactor, is tagged
  [`first-complete-proof`](https://github.com/alok/JordanCurveTheorem/tree/first-complete-proof).
