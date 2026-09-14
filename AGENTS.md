# Project contract

Formalize the full published Kanovei–Reeken argument in Lean 4, including the finite
polygonal Jordan theorem and the required nonstandard foundations.

- Use Linear project `JordanCurveTheorem`, completion issue `ALOK-911`.
- Work on the actual continuous-embedding theorem. Never assume the desired separation,
  boundary, connectivity, or polygon-approximation conclusions as input to the final theorem.
- No `sorry`, `admit`, custom axioms, opaque proofs without bodies, or `native_decide`.
- Keep unfinished claims in the dependency ledger or as explicitly named proposition definitions;
  they are not certified theorems. A clean build does not establish an uninhabited target.
- Use upstream mathlib at the pinned revision. Do not depend on local absolute paths or
  another checkout's build directory.
- Search before proving. Check edits with Lean and run the full build at checkpoints.
- Audit theorem axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
- Keep source correspondence precise: published paper first, arXiv as a secondary reference.
- The published paper has typographical slips. Record justified mathematical corrections
  in `docs/source-map.md` rather than silently reproducing false statements.
