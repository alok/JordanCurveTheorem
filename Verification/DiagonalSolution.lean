import Reeken.Geometry.PrePolygonDiagonal

open Set

namespace Verification

/-- Every simple polygon with at least four vertices has
an internal diagonal between existing, nonadjacent vertices. -/
theorem polygon_internal_diagonal {m : ℕ} (hm : 0 < m)
    (v : ZMod (m + 3) → EuclideanSpace ℝ (Fin 2)) (hv : Function.Injective v)
    (he : ∀ i j : ZMod (m + 3), i ≠ j →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) ⊆ {v i, v (i + 1)}) :
    let C := ⋃ i : ZMod (m + 3), segment ℝ (v i) (v (i + 1))
    ∃ i j : ZMod (m + 3), j ≠ i ∧ j ≠ i + 1 ∧ j ≠ i - 1 ∧
      ∀ x ∈ openSegment ℝ (v i) (v j),
        x ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ x) := by
  let P : Schoenflies.PrePolygon m := ⟨v, hv, he⟩
  exact Reeken.Geometry.exists_internal_diagonal_prePolygon P hm

end Verification
