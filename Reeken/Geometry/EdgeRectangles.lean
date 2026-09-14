import Schoenflies.Strip
import Reeken.Geometry.NearestSegments

/-! # The narrow rectangles in Lemma 3

For a directed edge of length `l`, the rectangle extends `2 * ε` beyond both
ends and on both sides. Its dimensions are therefore `(l + 4 * ε) × (4 * ε)`.
The closed ε-neighborhood of the edge lies in the open rectangle. Every point
of the closed rectangle is within `l + 4 * ε` of the initial endpoint; this
also bounds all shortest connections drawn from rectangle intersections.
-/

open Set Metric Schoenflies

namespace Reeken.Geometry

noncomputable def closedEdgeRectangle (a u : Plane) (l ε : ℝ) : Set Plane :=
  {x | -2 * ε ≤ Plane.coordAlong a u x ∧ Plane.coordAlong a u x ≤ l + 2 * ε ∧
    -2 * ε ≤ Plane.coordAcross a u x ∧ Plane.coordAcross a u x ≤ 2 * ε}

noncomputable def openEdgeRectangle (a u : Plane) (l ε : ℝ) : Set Plane :=
  Plane.strip a u (-2 * ε) (l + 2 * ε) (-2 * ε) (2 * ε)

theorem isOpen_openEdgeRectangle (a u : Plane) (l ε : ℝ) :
    IsOpen (openEdgeRectangle a u l ε) := Plane.isOpen_strip _ _ _ _ _ _

theorem isClosed_closedEdgeRectangle (a u : Plane) (l ε : ℝ) :
    IsClosed (closedEdgeRectangle a u l ε) := by
  have he : closedEdgeRectangle a u l ε =
      {x | -2 * ε ≤ Plane.coordAlong a u x} ∩
      ({x | Plane.coordAlong a u x ≤ l + 2 * ε} ∩
      ({x | -2 * ε ≤ Plane.coordAcross a u x} ∩
      {x | Plane.coordAcross a u x ≤ 2 * ε})) := rfl
  rw [he]
  exact (isClosed_le continuous_const (Plane.continuous_coordAlong a u)).inter
    ((isClosed_le (Plane.continuous_coordAlong a u) continuous_const).inter
      ((isClosed_le continuous_const (Plane.continuous_coordAcross a u)).inter
        (isClosed_le (Plane.continuous_coordAcross a u) continuous_const)))

theorem openEdgeRectangle_subset_closed (a u : Plane) (l ε : ℝ) :
    openEdgeRectangle a u l ε ⊆ closedEdgeRectangle a u l ε :=
  fun _ h ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

theorem mem_closedEdgeRectangle_param {a u : Plane} (hu : Plane.IsDirection u)
    {l ε t s : ℝ} :
    a + t • u + s • Plane.perp u ∈ closedEdgeRectangle a u l ε ↔
      -2 * ε ≤ t ∧ t ≤ l + 2 * ε ∧ -2 * ε ≤ s ∧ s ≤ 2 * ε := by
  simp only [closedEdgeRectangle, mem_ofPred_eq,
    Plane.coordAlong_param hu, Plane.coordAcross_param hu]

/-- Coordinates of every point on the central edge. -/
theorem edge_rectangle_coordinates {a u x : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) (hx : x ∈ segment ℝ a (a + l • u)) :
    Plane.coordAlong a u x ∈ Icc 0 l ∧ Plane.coordAcross a u x = 0 := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have he : AffineMap.lineMap a (a + l • u) t = a + (t * l) • u + (0 : ℝ) • Plane.perp u := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [he]
  have htAlong : Plane.coordAlong a u (a + (t * l) • u + (0 : ℝ) • Plane.perp u) = t * l :=
    Plane.coordAlong_param hu a (t * l) 0
  have htAcross : Plane.coordAcross a u (a + (t * l) • u + (0 : ℝ) • Plane.perp u) = 0 :=
    Plane.coordAcross_param hu a (t * l) 0
  rw [htAlong, htAcross]
  exact ⟨⟨mul_nonneg ht.1 hl, mul_le_of_le_one_left hl ht.2⟩, rfl⟩

/-- The ε-neighborhood fits strictly within the rectangle padded by 2ε. -/
theorem mem_openEdgeRectangle_of_near_edge {a u x y : Plane} (hu : Plane.IsDirection u)
    {l ε : ℝ} (hl : 0 ≤ l) (hε : 0 < ε)
    (hy : y ∈ segment ℝ a (a + l • u)) (hxy : dist x y ≤ ε) :
    x ∈ openEdgeRectangle a u l ε := by
  obtain ⟨hyAlong, hyAcross⟩ := edge_rectangle_coordinates hu hl hy
  have hAlong := abs_le.mp ((Plane.abs_coordAlong_sub_le hu a x y).trans hxy)
  have hAcross := abs_le.mp ((Plane.abs_coordAcross_sub_le hu a x y).trans hxy)
  change -2 * ε < Plane.coordAlong a u x ∧ Plane.coordAlong a u x < l + 2 * ε ∧
    -2 * ε < Plane.coordAcross a u x ∧ Plane.coordAcross a u x < 2 * ε
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hyAlong.1, hyAlong.2]

theorem dist_initial_le_of_mem_closedEdgeRectangle {a u x : Plane} (hu : Plane.IsDirection u)
    {l ε : ℝ} (hl : 0 ≤ l) (hx : x ∈ closedEdgeRectangle a u l ε) :
    dist x a ≤ l + 4 * ε := by
  have hAlong : |Plane.coordAlong a u x| ≤ l + 2 * ε :=
    abs_le.mpr ⟨by linarith [hx.1], hx.2.1⟩
  have hAcross : |Plane.coordAcross a u x| ≤ 2 * ε :=
    abs_le.mpr ⟨by linarith [hx.2.2.1], hx.2.2.2⟩
  have he : x - a = Plane.coordAlong a u x • u + Plane.coordAcross a u x • Plane.perp u := by
    have h := Plane.frame_decomp hu a x
    nth_rewrite 1 [h]
    module
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖Plane.coordAlong a u x • u‖ + ‖Plane.coordAcross a u x • Plane.perp u‖ := norm_add_le _ _
    _ = |Plane.coordAlong a u x| + |Plane.coordAcross a u x| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Plane.norm_perp, hu.norm]
      ring
    _ ≤ l + 4 * ε := by linarith

theorem isCompact_closedEdgeRectangle (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) (ε : ℝ) : IsCompact (closedEdgeRectangle a u l ε) :=
  (isCompact_closedBall a (l + 4 * ε)).of_isClosed_subset
    (isClosed_closedEdgeRectangle a u l ε)
    (fun _ hx ↦ dist_initial_le_of_mem_closedEdgeRectangle hu hl hx)

/-- Every shortest boundary connection from the rectangle is correspondingly short. -/
theorem nearest_dist_le_of_mem_closedEdgeRectangle {C : Set Plane} {a u x y : Plane}
    (ha : a ∈ C) (hu : Plane.IsDirection u) {l ε : ℝ} (hl : 0 ≤ l)
    (hx : x ∈ closedEdgeRectangle a u l ε) (hy : IsNearest C x y) :
    dist x y ≤ l + 4 * ε :=
  (hy.2 a ha).trans (dist_initial_le_of_mem_closedEdgeRectangle hu hl hx)

end Reeken.Geometry
