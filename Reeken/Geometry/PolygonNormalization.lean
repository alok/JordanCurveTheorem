/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The normalization induction below strengthens the finite normalization argument
in Schoenflies.Realization by retaining the vertex count and vertex inclusion.
-/
import Schoenflies.Realization

/-! # Normalization with a decreasing vertex count

Removing redundant vertices preserves the carrier, never increases the number
of vertices, and introduces no new vertices. These bounds support finite polygon
induction after a diagonal cut.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem exists_closedPolygon_le_of_prePolygon :
    ∀ (m : ℕ) (P : PrePolygon m), ∃ (n : ℕ) (Q : ClosedPolygon n),
      n ≤ m ∧ Q.carrier = P.carrier ∧ range Q.vertex ⊆ range P.vertex := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P
    by_cases hc : ∀ i, Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) ≠ 0
    · exact ⟨m, ⟨P.vertex, P.vertex_inj, P.edges_meet, hc⟩, le_rfl, rfl, subset_rfl⟩
    push Not at hc
    obtain ⟨i, hi⟩ := hc
    have hcol : (P.rotate (i + 1)).vertex (-1) ∈
        openSegment ℝ ((P.rotate (i + 1)).vertex (-1 - 1)) ((P.rotate (i + 1)).vertex 0) := by
      simp only [PrePolygon.rotate_vertex]
      rw [show i + 1 + (-1) = i by ring, show i + 1 + (-1 - 1) = i - 1 by ring,
        add_zero]
      exact PrePolygon.mem_openSegment_of_det_eq_zero i hi
    cases m with
    | zero => exact False.elim (PrePolygon.not_collinear_triangle (P.rotate (i + 1)) hcol)
    | succ m =>
      obtain ⟨n, Q, hn, hQ, hvertices⟩ := ih m (by omega)
        (PrePolygon.deleteLast (P.rotate (i + 1)) hcol)
      refine ⟨n, Q, by omega, ?_, ?_⟩
      · rw [hQ, PrePolygon.carrier_deleteLast, PrePolygon.carrier_rotate]
      · intro x hx
        obtain ⟨j, rfl⟩ := hvertices hx
        exact ⟨i + 1 + PrePolygon.emb j, rfl⟩

end Reeken.Geometry
