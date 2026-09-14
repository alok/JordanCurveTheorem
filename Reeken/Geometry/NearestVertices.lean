import Reeken.Geometry.PointArcs
import Mathlib.Data.Finset.Max

/-! # Nearest vertices for the finite barrier calculation

Replacing a nearest point on the polygon by an endpoint of its edge costs at
most one maximum edge length. This makes the two candidate arcs actual lists
of existing polygon edges.
-/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : SimpleLoop E} (p : InscribedPolygon f)

noncomputable def nearestVertex (x : E) : Fin (p.n + 1) := by
  classical
  exact Classical.choose (Finset.univ.exists_min_image (fun j ↦ dist x (p.vertex j)) Finset.univ_nonempty)

omit [NormedSpace ℝ E] in
theorem nearestVertex_dist_le (x : E) (j : Fin (p.n + 1)) :
    dist x (p.vertex (p.nearestVertex x)) ≤ dist x (p.vertex j) := by
  classical
  exact (Classical.choose_spec (Finset.univ.exists_min_image
    (fun j ↦ dist x (p.vertex j)) Finset.univ_nonempty)).2 j (Finset.mem_univ j)

theorem nearestVertex_dist_le_of_near_trace {x y : E} (hy : y ∈ p.trace) :
    dist x (p.vertex (p.nearestVertex x)) ≤ dist x y + p.maxEdge := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  have hnear : dist y (p.vertex j) ≤ p.maxEdge := by
    rw [dist_comm]
    exact (dist_left_le_of_mem_segment hj).trans (p.edgeLength_le_maxEdge j)
  exact (p.nearestVertex_dist_le x j).trans
    ((dist_triangle x y (p.vertex j)).trans (by linarith))

end Reeken.Geometry.InscribedPolygon
