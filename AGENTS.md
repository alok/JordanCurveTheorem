# Project contract

Formalize the full published Kanovei–Reeken argument in Lean 4, including the finite
polygonal Jordan theorem and the required nonstandard foundations.

- Use Linear project `JordanCurveTheorem`, completion issue `ALOK-911`.
- Work on the actual continuous-embedding theorem. Never assume the desired separation,
  boundary, connectivity, or polygon-approximation conclusions as input to the final theorem.
- No `sorry`, `admit`, custom axioms, opaque proofs without bodies, or `native_decide`.
  The sole exception is `Verification/*Challenge.lean`: trusted Comparator statements contain
  explicit challenge holes. They must never be imported into `Reeken` or a solution module.
- Keep unfinished claims in the dependency ledger or as explicitly named proposition definitions;
  they are not certified theorems. A clean build does not establish an uninhabited target.
- Use upstream mathlib at the pinned revision. Do not depend on local absolute paths or
  another checkout's build directory.
- Search before proving. Check edits with Lean and run the full build at checkpoints.
- Audit theorem axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
  Run Comparator with Nanoda on a clean Linux checkout as requested by the user. Keep challenge
  statements independent of project definitions. Use Lean Beam for interactive probes and a
  Verso-compatible blueprint for dependencies; never present planned checks as passed.
- Keep source correspondence precise: published paper first, arXiv as a secondary reference.
- The published paper has typographical slips. Record justified mathematical corrections
  in `docs/source-map.md` rather than silently reproducing false statements.
