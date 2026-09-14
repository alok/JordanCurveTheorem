import Schoenflies.Subdivide

/-! # Choosing the smaller of two boundary arcs

Comparing distances by domination avoids selecting a separate radius for each
arc. The selected set lies in any ball that contains either candidate.
Thus the choice can be made uniformly before choosing a standard error bound.
-/

open Set Metric Schoenflies

namespace Reeken.Geometry

variable {E : Type*} [MetricSpace E]

def RadiusLE (a : E) (s t : Set E) : Prop :=
  ∀ x ∈ s, ∃ y ∈ t, dist x a ≤ dist y a

open scoped Classical in
noncomputable def smallerRadiusSet (a : E) (s t : Set E) : Set E :=
  if RadiusLE a s t then s else t

theorem radiusLE_of_not_radiusLE {a : E} {s t : Set E} (h : ¬ RadiusLE a s t) :
    RadiusLE a t s := by
  unfold RadiusLE at h ⊢
  push Not at h
  obtain ⟨x, hx, hdist⟩ := h
  exact fun y hy ↦ ⟨x, hx, (hdist y hy).le⟩

theorem smallerRadiusSet_subset_ball_of_left {a : E} {s t : Set E} {r : ℝ}
    (h : s ⊆ ball a r) : smallerRadiusSet a s t ⊆ ball a r := by
  classical
  unfold smallerRadiusSet
  split_ifs with hst
  · exact h
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := radiusLE_of_not_radiusLE hst y hy
    exact hxy.trans_lt (h hx)

theorem smallerRadiusSet_subset_ball_of_right {a : E} {s t : Set E} {r : ℝ}
    (h : t ⊆ ball a r) : smallerRadiusSet a s t ⊆ ball a r := by
  classical
  unfold smallerRadiusSet
  split_ifs with hst
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hst x hx
    exact hxy.trans_lt (h hy)
  · exact h

open scoped Classical in
noncomputable def smallerRadiusPieces (a : Plane) (L M : List Piece) : List Piece :=
  if RadiusLE a (cover L) (cover M) then L else M

theorem cover_smallerRadiusPieces (a : Plane) (L M : List Piece) :
    cover (smallerRadiusPieces a L M) = smallerRadiusSet a (cover L) (cover M) := by
  classical
  unfold smallerRadiusPieces smallerRadiusSet
  split_ifs <;> rfl

end Reeken.Geometry
