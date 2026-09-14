# Finite polygonal foundation

These files include the transitive import closure of `Schoenflies.FaceCyclesLand` (including `Schoenflies.PrePolygonSep`) from
[Álvaro Begué's schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean),
commit `05a43d29cde026618777db3d4e4316204ccca237`.

They retain the original copyright headers and Apache 2.0 license, copied as
`LICENSE.Schoenflies`. This is third-party proof code, not original project work.

The selected 47 modules contain the finite polygonal Jordan theorem, finite polygonal
crosscuts at arbitrary cut points, collinear-vertex normalization, finite plane-graph
face cycles, and their prerequisites. The general
Jordan and Schoenflies assembly modules are excluded. The intended use is the finite
polygonal foundation assumed in Kanovei–Reeken's nonstandard argument.

Four additional modules contain finite excerpts from that same revision. They preserve
the upstream declaration names and proofs, with the compatibility changes below:

| Local module | Upstream source and included declarations |
| --- | --- |
| `SquareFrontier.lean` | `SquareMover.lean`: `abs_sub_le_supDist`, `supDist_le_of_forall`, `exists_abs_sub_eq_of_supDist_eq`, `add_smul_single_apply`, `dist_add_smul_single`, `interior_closedSquare`, and `frontier_closedSquare` |
| `SquarePieces.lean` | `ModelCurve.lean`: `mem_segment_horiz` and `mem_segment_vert`; `ArcComplementPrep.lean`: the initial `Plane` namespace of square coordinates and side membership, then `squarePieces`, `cover_squarePieces`, and `squarePieces_nondeg` |
| `SquarePolygon.lean` | `ArcComplementPrep.lean`: `squarePolygon` through `carrier_squarePolygon`, then `isJordanCurve_frontier_closedSquare` and `isPolygonal_frontier_closedSquare` |
| `Graph/Trace.lean` | `CommonSubdivision.lean`: its initial `Graph` namespace, from `connected_of_isPreconnected_pointSet` through `IsTwoConnected.spanning_mono` |

These excerpts do not import the source's point mover, arc-complement construction,
cell-structure transfer, or general Jordan/Schoenflies assembly. There are 51 local
vendor modules in total: 47 complete modules in the original finite closure and these
four excerpts. The original graph-deletion criterion in `Reeken/Geometry/DrawingDeletion.lean`
is separate from this attributed code.

The source pins Lean 4.32.2. This project checks the selected code with Lean 4.33.1
and its own pinned upstream mathlib. Compatibility edits, if needed, are recorded here.
The vendor library retains the source's auto-implicit setting independently of Reeken.

Compatibility edits so far: rename deprecated `mem_setOf_eq` to `mem_ofPred_eq`;
make the unit-interval/reparametrization unfolding explicit in `Subarc.image_reparam_I`;
use `have` for proposition-valued local instances in `Realization.lean`,
`Graph/Tree.lean`, `Graph/Trace.lean`, and `FaceCyclesProof.lean`; and rename
`Graph.edgeSet_eq_setOf_exists_isLink` to `Graph.edgeSet_eq_setOfPred_exists_isLink`.

The selected modules and `Reeken.Geometry.PolygonSeparation` adapter have passed a
warning-free local build on the pinned toolchain. The project axiom audit includes
every declaration defined in these modules, including private helpers and declarations
in the root `Graph` namespace. `Verification/SeparationChallenge.lean` independently states the
finite conclusion for Comparator/Nanoda; CI records the result of that separate check.
Finite interior simple connectivity, the final Jordan theorem, and the remaining
nonstandard limiting constructions are not claimed by this integration.
