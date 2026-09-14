import Reeken.Geometry.EdgeReplacementParity
import Reeken.Geometry.Segments

/-! # Uniform size of an edge closed against a nearby boundary arc -/

open Set Schoenflies

namespace Reeken.Geometry

theorem edgeBarrier_dist_le {foot : Plane → Plane} {arc : Piece → List Piece}
    {P : Piece} {r : ℝ} (hr : 0 ≤ r) (hedge : dist P.1 P.2 ≤ r)
    (hleft : dist P.1 (foot P.1) ≤ r) (hright : dist P.2 (foot P.2) ≤ r)
    (harc : ∀ z ∈ cover (arc P), dist z (foot P.1) ≤ r) :
    ∀ z ∈ cover (edgeBarrier foot arc P), dist z (foot P.1) ≤ 3 * r := by
  simp only [edgeBarrier, cover_append, cover_cons, cover_nil, union_empty, Piece.seg]
  rintro z ((hz | hz | hz) | hz)
  · have hzleft := dist_left_le_of_mem_segment hz
    have ht := dist_triangle z P.1 (foot P.1)
    rw [dist_comm P.1 z] at hzleft
    linarith
  · have hzright := dist_left_le_of_mem_segment hz
    have ht₁ := dist_triangle z P.2 (foot P.1)
    have ht₂ := dist_triangle P.2 P.1 (foot P.1)
    rw [dist_comm P.2 z] at hzright
    rw [dist_comm P.2 P.1] at ht₂
    linarith
  · have hzleft := dist_left_le_of_mem_segment hz
    rw [dist_comm (foot P.1) z, dist_comm (foot P.1) P.1] at hzleft
    linarith
  · linarith [harc z hz]

end Reeken.Geometry
