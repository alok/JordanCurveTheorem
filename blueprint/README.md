# Verso blueprint

The blueprint links to the actual compiled Reeken declarations and displays the remaining
proof obligations in a dependency graph. Its renderer and dependencies are pinned in the
manifest. It uses the root project's Lean 4.33.1 and mathlib revision.

Run from this directory (the generator uses its current working directory):

```sh
lake update
lake exe cache get Mathlib.Analysis.Normed.Affine.Convex
lake exe vbp build
```

The generated site is `_out/site/html-multi/index.html`; the dependency graph is
`_out/site/html-multi/Dependency-Graph/index.html`.

The blueprint has been built locally. It does not make open mathematical nodes into Lean
theorems. The full Jordan theorem and the post-proof refactoring phase remain unfinished.
