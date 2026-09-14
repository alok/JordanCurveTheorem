import Reeken.Geometry.ArcIntersection
import Reeken.Geometry.SquareAnnulus
import Mathlib.Topology.Order.IntermediateValue

/-! # The two polygon arcs cross a local square at distinct points

One cut vertex is strictly inside the square and the other is strictly outside.
Continuity along each arc gives a crossing. Simplicity and the strict endpoint
conditions force the two crossings to differ.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem exists_square_crossing {s : Set Plane} (hs : IsPreconnected s)
    {a b c : Plane} {r : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (har : Plane.supDist a c ≤ r) (hbr : r ≤ Plane.supDist b c) :
    (s ∩ squareBoundary c r).Nonempty := by
  obtain ⟨x, hx, he⟩ := hs.intermediate_value₂ ha hb
    (continuous_supDist_left c).continuousOn continuous_const.continuousOn har hbr
  exact ⟨x, hx, he⟩

namespace InscribedPolygon

variable {f : SimpleLoop Plane} {p : InscribedPolygon f}

/-- Both arcs hit the square, and their hit points are different. -/
theorem Simple.exists_distinct_square_crossings (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) {c : Plane} {r : ℝ}
    (ha : p.vertex a ∈ Plane.openSquare c r)
    (hb : p.vertex b ∉ Plane.closedSquare c r) :
    ∃ x ∈ p.forwardArc a b ∩ squareBoundary c r,
      ∃ y ∈ p.backwardArc a b ∩ squareBoundary c r, x ≠ y := by
  have har : Plane.supDist (p.vertex a) c < r := ha
  have hbr : r < Plane.supDist (p.vertex b) c := lt_of_not_ge hb
  obtain ⟨x, hxF, hxS⟩ := exists_square_crossing
    (p.isPathConnected_forwardArc a b).isConnected.isPreconnected
    (Or.inl rfl) (p.joinedIn_forwardArc hab le_rfl).target_mem har.le hbr.le
  obtain ⟨y, hyB, hyS⟩ := exists_square_crossing
    (p.isPathConnected_backwardArc a b).isConnected.isPreconnected
    (p.joinedIn_backwardArc (Or.inl le_rfl)).target_mem (Or.inl rfl) har.le hbr.le
  refine ⟨x, ⟨hxF, hxS⟩, y, ⟨hyB, hyS⟩, ?_⟩
  intro he
  have hx : x ∈ p.forwardArc a b ∩ p.backwardArc a b := ⟨hxF, he ▸ hyB⟩
  rw [hp.arcs_inter hab] at hx
  rcases hx with rfl | rfl
  · exact har.ne hxS
  · exact hbr.ne hxS.symm

end InscribedPolygon
end Reeken.Geometry
