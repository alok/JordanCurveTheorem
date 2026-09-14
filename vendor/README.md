# Finite polygonal foundation

These files are the transitive import closure of `Schoenflies.PrePolygonSep` from
[Álvaro Begué's schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean),
commit `05a43d29cde026618777db3d4e4316204ccca237`.

They retain the original copyright headers and Apache 2.0 license, copied as
`LICENSE.Schoenflies`. This is third-party proof code, not original project work.

The selected 36 modules contain the finite polygonal Jordan theorem, finite polygonal
crosscuts, collinear-vertex normalization, and their prerequisites. The general
Jordan and Schoenflies assembly modules are excluded. The intended use is the finite
polygonal foundation assumed in Kanovei–Reeken's nonstandard argument.

The source pins Lean 4.32.2. This project checks the selected code with Lean 4.33.1
and its own pinned upstream mathlib. Compatibility edits, if needed, are recorded here.
The vendor library retains the source's auto-implicit setting independently of Reeken.

Compatibility edits so far: rename deprecated `mem_setOf_eq` to `mem_ofPred_eq`;
make the unit-interval/reparametrization unfolding explicit in `Subarc.image_reparam_I`;
and use `have` for two proposition-valued local instances in `Realization.lean`.

The selected modules and `Reeken.Geometry.PolygonSeparation` adapter have passed a
warning-free local build on the pinned toolchain. The project axiom audit includes
both namespaces. `Verification/SeparationChallenge.lean` independently states the
finite conclusion for Comparator/Nanoda; CI records the result of that separate check.
Finite interior simple connectivity, the final Jordan theorem, and the remaining
nonstandard limiting constructions are not claimed by this integration.
