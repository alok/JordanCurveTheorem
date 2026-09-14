import Reeken.Geometry.EdgeRectangles
import Schoenflies.SquarePolygon

/-! # Rectangles as affine images of the square

This identifies the actual four-sided boundary needed by the finite arrangement,
including its simple closed parametrization and polygonal presentation.
-/

open Set Schoenflies

namespace Reeken.Geometry

noncomputable def rectangleHomeomorph (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) : Plane ≃ₜ Plane where
  toFun z := a + (l / 2 + (l / 2 + 2 * ε) * z 0) • u + (2 * ε * z 1) • Plane.perp u
  invFun x := Plane.mk ((Plane.coordAlong a u x - l / 2) / (l / 2 + 2 * ε))
    (Plane.coordAcross a u x / (2 * ε))
  left_inv z := by
    have hL : l / 2 + 2 * ε ≠ 0 := ne_of_gt (by linarith)
    have hE : 2 * ε ≠ 0 := ne_of_gt (by positivity)
    apply PiLp.ext
    intro j
    fin_cases j
    · change (Plane.coordAlong a u _ - l / 2) / (l / 2 + 2 * ε) = z 0
      rw [Plane.coordAlong_param hu]
      field_simp
      ring
    · change Plane.coordAcross a u _ / (2 * ε) = z 1
      rw [Plane.coordAcross_param hu]
      field_simp
  right_inv x := by
    have hL : l / 2 + 2 * ε ≠ 0 := ne_of_gt (by linarith)
    have hE : 2 * ε ≠ 0 := ne_of_gt (by positivity)
    change a + (l / 2 + (l / 2 + 2 * ε) *
        ((Plane.coordAlong a u x - l / 2) / (l / 2 + 2 * ε))) • u +
      (2 * ε * (Plane.coordAcross a u x / (2 * ε))) • Plane.perp u = x
    have h1 : l / 2 + (l / 2 + 2 * ε) *
        ((Plane.coordAlong a u x - l / 2) / (l / 2 + 2 * ε)) = Plane.coordAlong a u x := by
      field_simp
      ring
    have h2 : 2 * ε * (Plane.coordAcross a u x / (2 * ε)) = Plane.coordAcross a u x := by
      field_simp
    rw [h1, h2]
    exact (Plane.frame_decomp hu a x).symm
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hA := Plane.continuous_coordAlong a u
    have hB := Plane.continuous_coordAcross a u
    fun_prop

private theorem scaled_mem_Icc_iff {r t c : ℝ} (hr : 0 < r) :
    (c - r ≤ c + r * t ∧ c + r * t ≤ c + r) ↔ |t| ≤ 1 := by
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_le_mul_iff_right₀ hr).mp (by linarith), (mul_le_mul_iff_right₀ hr).mp (by linarith)⟩
  · rintro ⟨h1, h2⟩
    have h1' := (mul_le_mul_iff_right₀ hr).mpr h1
    have h2' := (mul_le_mul_iff_right₀ hr).mpr h2
    exact ⟨by linarith, by linarith⟩

theorem rectangleHomeomorph_preimage_closed (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) :
    rectangleHomeomorph a hu hl hε ⁻¹' closedEdgeRectangle a u l ε = Plane.closedSquare 0 1 := by
  ext z
  change (-2 * ε ≤ Plane.coordAlong a u
      (a + (l / 2 + (l / 2 + 2 * ε) * z 0) • u + (2 * ε * z 1) • Plane.perp u) ∧
    Plane.coordAlong a u
      (a + (l / 2 + (l / 2 + 2 * ε) * z 0) • u + (2 * ε * z 1) • Plane.perp u) ≤ l + 2 * ε ∧
    -2 * ε ≤ Plane.coordAcross a u
      (a + (l / 2 + (l / 2 + 2 * ε) * z 0) • u + (2 * ε * z 1) • Plane.perp u) ∧
    Plane.coordAcross a u
      (a + (l / 2 + (l / 2 + 2 * ε) * z 0) • u + (2 * ε * z 1) • Plane.perp u) ≤ 2 * ε) ↔ _
  rw [Plane.coordAlong_param hu, Plane.coordAcross_param hu]
  change (-2 * ε ≤ l / 2 + (l / 2 + 2 * ε) * z 0 ∧
      l / 2 + (l / 2 + 2 * ε) * z 0 ≤ l + 2 * ε ∧
      -2 * ε ≤ 2 * ε * z 1 ∧ 2 * ε * z 1 ≤ 2 * ε) ↔ Plane.supDist z 0 ≤ 1
  simp only [Plane.supDist, sub_zero, Plane.supNorm, max_le_iff]
  have hA := scaled_mem_Icc_iff (t := z 0) (c := l / 2) (r := l / 2 + 2 * ε) (by linarith)
  have hB := scaled_mem_Icc_iff (t := z 1) (c := 0) (r := 2 * ε) (by positivity)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hA.mp ⟨by linarith, by linarith⟩, hB.mp ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨ha1, ha2⟩ := hA.mpr h1
    obtain ⟨h3, h4⟩ := hB.mpr h2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem rectangleHomeomorph_image_closed (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) :
    rectangleHomeomorph a hu hl hε '' Plane.closedSquare 0 1 = closedEdgeRectangle a u l ε := by
  rw [← rectangleHomeomorph_preimage_closed a hu hl hε]
  exact (rectangleHomeomorph a hu hl hε).surjective.image_preimage _

theorem rectangleHomeomorph_image_frontier (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) :
    rectangleHomeomorph a hu hl hε '' frontier (Plane.closedSquare 0 1) =
      frontier (closedEdgeRectangle a u l ε) := by
  rw [Homeomorph.image_frontier, rectangleHomeomorph_image_closed]

theorem rectangleHomeomorph_lineMap (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (x y : Plane) (t : ℝ) :
    rectangleHomeomorph a hu hl hε (AffineMap.lineMap x y t) =
      AffineMap.lineMap (rectangleHomeomorph a hu hl hε x) (rectangleHomeomorph a hu hl hε y) t := by
  change a + (l / 2 + (l / 2 + 2 * ε) * (AffineMap.lineMap x y t) 0) • u +
      (2 * ε * (AffineMap.lineMap x y t) 1) • Plane.perp u = _
  simp only [rectangleHomeomorph, AffineMap.lineMap_apply_module]
  apply PiLp.ext
  intro j
  simp
  ring

theorem rectangleHomeomorph_image_segment (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) (x y : Plane) :
    rectangleHomeomorph a hu hl hε '' segment ℝ x y =
      segment ℝ (rectangleHomeomorph a hu hl hε x) (rectangleHomeomorph a hu hl hε y) := by
  simp only [segment_eq_image_lineMap, image_image]
  congr 1
  funext t
  exact rectangleHomeomorph_lineMap a hu hl hε x y t

private theorem image_poly_of_image_segments (g : Plane → Plane)
    (hseg : ∀ x y, g '' segment ℝ x y = segment ℝ (g x) (g y)) :
    ∀ vs : List Plane, g '' poly vs = poly (vs.map g)
  | [] => by simp
  | [v] => by simp
  | v :: w :: vs => by
    rw [poly_cons_cons, image_union, hseg, image_poly_of_image_segments g hseg (w :: vs)]
    rfl

theorem isJordanCurve_frontier_closedEdgeRectangle (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) :
    IsJordanCurve (frontier (closedEdgeRectangle a u l ε)) := by
  let e := rectangleHomeomorph a hu hl hε
  obtain ⟨g, hg, hgi⟩ := isJordanCurve_frontier_closedSquare (0 : Plane) zero_lt_one
  refine ⟨e ∘ g, ⟨e.continuous.comp_continuousOn hg.continuousOn,
    congrArg e hg.closes, fun x hx y hy hxy ↦ hg.injOn hx hy (e.injective hxy)⟩, ?_⟩
  rw [image_comp, hgi]
  exact rectangleHomeomorph_image_frontier a hu hl hε

theorem isPolygonal_frontier_closedEdgeRectangle (a : Plane) {u : Plane} (hu : Plane.IsDirection u)
    {l : ℝ} (hl : 0 ≤ l) {ε : ℝ} (hε : 0 < ε) :
    IsPolygonal (frontier (closedEdgeRectangle a u l ε)) := by
  obtain ⟨vs, hvs⟩ := isPolygonal_frontier_closedSquare (0 : Plane) zero_lt_one
  refine ⟨vs.map (rectangleHomeomorph a hu hl hε), ?_⟩
  rw [← image_poly_of_image_segments _ (rectangleHomeomorph_image_segment a hu hl hε), ← hvs]
  exact (rectangleHomeomorph_image_frontier a hu hl hε).symm

end Reeken.Geometry
