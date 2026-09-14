import Reeken.Geometry.TriangleContraction
import Mathlib.Analysis.Convex.Combination

/-! # Signed-area coordinates in a triangle

The three signed-area ratios add to one and reconstruct the point. Positivity
of all three ratios places the point in the ordinary interior of the convex hull.
These formulas also describe small motions across an edge of a triangle.
-/

open Set Schoenflies

namespace Reeken.Geometry

noncomputable def triangleWeights (a b c x : Plane) : Fin 3 → ℝ :=
  ![Plane.det (b - x) (c - x) / Plane.det (b - a) (c - a),
    Plane.det (c - x) (a - x) / Plane.det (b - a) (c - a),
    Plane.det (a - x) (b - x) / Plane.det (b - a) (c - a)]

theorem triangleWeights_sum {a b c : Plane} (h : Plane.det (b - a) (c - a) ≠ 0) (x : Plane) :
    ∑ i, triangleWeights a b c x i = 1 := by
  simp [triangleWeights, Fin.sum_univ_succ]
  field_simp [h]
  simp [Plane.det]
  ring

theorem triangleWeights_decompose {a b c : Plane} (h : Plane.det (b - a) (c - a) ≠ 0) (x : Plane) :
    ∑ i, triangleWeights a b c x i • ![a, b, c] i = x := by
  apply PiLp.ext
  intro j
  fin_cases j <;> simp [triangleWeights, Fin.sum_univ_succ]
  all_goals
    field_simp [h]
    simp [Plane.det]
    ring

theorem continuous_triangleWeights (a b c : Plane) (i : Fin 3) :
    Continuous (fun x ↦ triangleWeights a b c x i) := by
  fin_cases i <;> dsimp [triangleWeights, Plane.det] <;> fun_prop

theorem triangleWeights_combo (a b c x y : Plane) (u v : ℝ) (huv : u + v = 1) (i : Fin 3) :
    triangleWeights a b c (u • x + v • y) i =
      u * triangleWeights a b c x i + v * triangleWeights a b c y i := by
  rw [show u = 1 - v by linarith]
  fin_cases i <;> simp [triangleWeights, Plane.det] <;> ring

theorem triangleWeights_vertices {a b c : Plane} (h : Plane.det (b - a) (c - a) ≠ 0)
    (i j : Fin 3) : triangleWeights a b c (![a, b, c] i) j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [triangleWeights, Fin.ext_iff, h] <;>
    (try field_simp [h]) <;> simp [Plane.det] <;> ring

theorem triangleWeights_on_base {a b c x : Plane} (h : Plane.det (b - a) (c - a) ≠ 0)
    (hx : x ∈ openSegment ℝ b c) :
    triangleWeights a b c x 0 = 0 ∧ 0 < triangleWeights a b c x 1 ∧
      0 < triangleWeights a b c x 2 := by
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hx
  have hb : ∀ j, triangleWeights a b c b j = if (1 : Fin 3) = j then 1 else 0 :=
    triangleWeights_vertices h 1
  have hc : ∀ j, triangleWeights a b c c j = if (2 : Fin 3) = j then 1 else 0 :=
    triangleWeights_vertices h 2
  simp only [triangleWeights_combo a b c b c u v huv, hb, hc]
  norm_num [Fin.ext_iff]
  exact ⟨hu, hv⟩

theorem mem_triangle_hull_of_weights_nonneg {a b c x : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hw : ∀ i, 0 ≤ triangleWeights a b c x i) :
    x ∈ convexHull ℝ {a, b, c} := by
  have hp : ∀ i : Fin 3, ![a, b, c] i ∈ convexHull ℝ {a, b, c} := by
    intro i
    apply subset_convexHull ℝ _
    fin_cases i <;> simp
  have hs := (convex_convexHull ℝ ({a, b, c} : Set Plane)).sum_mem
    (t := Finset.univ) (w := triangleWeights a b c x) (z := ![a, b, c])
    (fun i _ ↦ hw i) (triangleWeights_sum h x) (fun i _ ↦ hp i)
  rwa [triangleWeights_decompose h x] at hs

theorem mem_interior_triangle_hull_of_weights_pos {a b c x : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hw : ∀ i, 0 < triangleWeights a b c x i) :
    x ∈ interior (convexHull ℝ {a, b, c}) := by
  have hop : IsOpen {y | ∀ i, 0 < triangleWeights a b c y i} := by
    have he : {y | ∀ i, 0 < triangleWeights a b c y i} =
        ⋂ i, {y | 0 < triangleWeights a b c y i} := by ext y; simp
    rw [he]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_triangleWeights a b c i)
  have hsub : {y | ∀ i, 0 < triangleWeights a b c y i} ⊆ convexHull ℝ {a, b, c} :=
    fun y hy ↦ mem_triangle_hull_of_weights_nonneg h (fun i ↦ (hy i).le)
  exact interior_maximal hsub hop hw

theorem exists_motion_from_base_into_triangle {a b c x y : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hx : x ∈ openSegment ℝ b c)
    (hy : 0 < triangleWeights a b c y 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (1 - ε) • x + ε • y ∈ interior (convexHull ℝ {a, b, c}) := by
  obtain ⟨hx0, hx1, hx2⟩ := triangleWeights_on_base h hx
  let f : ℝ → Plane := fun ε ↦ (1 - ε) • x + ε • y
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hop : IsOpen {ε : ℝ | 0 < triangleWeights a b c (f ε) 1 ∧
      0 < triangleWeights a b c (f ε) 2} :=
    (isOpen_lt continuous_const ((continuous_triangleWeights a b c 1).comp hf)).inter
      (isOpen_lt continuous_const ((continuous_triangleWeights a b c 2).comp hf))
  have hzero : (0 : ℝ) ∈ {ε : ℝ | 0 < triangleWeights a b c (f ε) 1 ∧
      0 < triangleWeights a b c (f ε) 2} := by simpa [f] using And.intro hx1 hx2
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hop 0 hzero
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hother := hball (a := ε) (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hε] using hεδ)
  apply mem_interior_triangle_hull_of_weights_pos h
  intro i
  fin_cases i
  · change 0 < triangleWeights a b c ((1 - ε) • x + ε • y) 0
    rw [triangleWeights_combo a b c x y (1 - ε) ε (by ring), hx0, mul_zero, zero_add]
    exact mul_pos hε hy
  · exact hother.1
  · exact hother.2

theorem eq_lineMap_of_triangleWeight_zero {a b c x : Plane}
    (h : Plane.det (b - a) (c - a) ≠ 0) (hx : triangleWeights a b c x 0 = 0) :
    x = AffineMap.lineMap b c (triangleWeights a b c x 2) := by
  have hs := triangleWeights_sum h x
  have hd := triangleWeights_decompose h x
  simp [Fin.sum_univ_succ] at hs hd
  change triangleWeights a b c x 0 + (triangleWeights a b c x 1 +
    triangleWeights a b c x 2) = 1 at hs
  change triangleWeights a b c x 0 • a + (triangleWeights a b c x 1 • b +
    triangleWeights a b c x 2 • c) = x at hd
  rw [hx, zero_smul, zero_add] at hd
  calc
    x = triangleWeights a b c x 1 • b + triangleWeights a b c x 2 • c := hd.symm
    _ = AffineMap.lineMap b c (triangleWeights a b c x 2) := by
      rw [AffineMap.lineMap_apply_module]
      congr 1
      congr 1
      linarith

end Reeken.Geometry
