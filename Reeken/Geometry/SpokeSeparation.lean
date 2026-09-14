import Reeken.Geometry.NearestSegments
import Reeken.Geometry.SmallEnclosures
import Mathlib.Analysis.InnerProductSpace.Convex

/-! # Two disjoint connections in a noninfinitesimal inner cell

If all its corner connections had the same foot, an inner polygon with short
connections would itself be small. An enclosed point farther from the outer
boundary rules this out. Distinct nearest feet give disjoint connections.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem exists_distinct_corner_feet {m : ℕ} (Q : ClosedPolygon m)
    {C : Set Plane} {foot : Plane → Plane} (hfoot : ∀ x, IsNearest C x (foot x))
    {x : Plane} (hx : x ∈ inside Q.carrier) {δ r : ℝ}
    (hfar : ∀ y ∈ C, δ ≤ dist x y) (hscale : Real.sqrt 2 * r < δ)
    (hshort : ∀ j, dist (Q.vertex j) (foot (Q.vertex j)) ≤ r) :
    ∃ j : ZMod (m + 3), foot (Q.vertex j) ≠ foot (Q.vertex 0) := by
  by_contra h
  push Not at h
  have hvertices : ∀ j, dist (Q.vertex j) (foot (Q.vertex 0)) ≤ r := by
    intro j
    rw [← h j]
    exact hshort j
  have hbound := dist_le_of_common_corner_foot Q hvertices hx
  have hdist := hfar (foot (Q.vertex 0)) (hfoot _).1
  linarith

theorem exists_disjoint_corner_connections {m : ℕ} (Q : ClosedPolygon m)
    {C : Set Plane} {foot : Plane → Plane} (hfoot : ∀ x, IsNearest C x (foot x))
    {x : Plane} (hx : x ∈ inside Q.carrier) {δ r : ℝ}
    (hfar : ∀ y ∈ C, δ ≤ dist x y) (hscale : Real.sqrt 2 * r < δ)
    (hshort : ∀ j, dist (Q.vertex j) (foot (Q.vertex j)) ≤ r) :
    ∃ j : ZMod (m + 3), foot (Q.vertex j) ≠ foot (Q.vertex 0) ∧
      Disjoint (segment ℝ (Q.vertex j) (foot (Q.vertex j)))
        (segment ℝ (Q.vertex 0) (foot (Q.vertex 0))) := by
  obtain ⟨j, hj⟩ := exists_distinct_corner_feet Q hfoot hx hfar hscale hshort
  exact ⟨j, hj, nearest_segments_disjoint_of_feet_ne (hfoot _) (hfoot _)
    (fun he ↦ hj (congrArg foot he)) hj⟩

end Reeken.Geometry
