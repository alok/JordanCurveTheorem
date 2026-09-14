import Reeken.Geometry.SmallEnclosures
import Reeken.Geometry.NondegenerateChains

/-! # Small closed barriers have the same crossing parity at distant points -/

open Set Metric Schoenflies

namespace Reeken.Geometry

theorem isPreconnected_compl_closedSquare (a : Plane) (r : ℝ) :
    IsPreconnected (Plane.closedSquare a r)ᶜ := by
  have heq : (fun w : Plane ↦ w + a) '' Plane.beyondSquare r = (Plane.closedSquare a r)ᶜ := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Plane.beyondSquare_eq_compl] at hw
      simpa only [Plane.closedSquare, mem_compl_iff, mem_ofPred_eq, Plane.supDist,
        add_sub_cancel_right, sub_zero] using hw
    · intro hx
      refine ⟨x - a, ?_, sub_add_cancel _ _⟩
      rw [Plane.beyondSquare_eq_compl]
      simpa only [Plane.closedSquare, mem_compl_iff, mem_ofPred_eq, Plane.supDist,
        sub_zero] using hx
  rw [← heq]
  exact (Plane.isConnected_beyondSquare r).isPreconnected.image _
    (continuous_id.add continuous_const).continuousOn

theorem not_mem_closedSquare_of_dist_gt {a x : Plane} {r : ℝ}
    (hx : Real.sqrt 2 * r < dist x a) : x ∉ Plane.closedSquare a r := by
  intro h
  have hdist : dist x a ≤ Real.sqrt 2 * r := by
    rw [dist_eq_norm]
    exact (Plane.norm_le_sqrt_two_mul_supNorm (x - a)).trans
      (mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _))
  exact hx.not_ge hdist

theorem parity_eq_far_from_small_chain {L : List Piece} (hclosed : IsClosedChain L)
    {u : Plane} (hu : Plane.IsDirection u)
    (hdir : ∀ P ∈ L, P.Nondeg → hgt u P.1 ≠ hgt u P.2)
    {a x y : Plane} {r : ℝ} (hL : ∀ z ∈ cover L, dist z a ≤ r)
    (hx : Real.sqrt 2 * r < dist x a) (hy : Real.sqrt 2 * r < dist y a) :
    parity u L x = parity u L y := by
  rw [← parity_nondegeneratePieces L u x, ← parity_nondegeneratePieces L u y]
  apply parity_eq_of_isPreconnected hu
    (fun P hP ↦ hdir P (mem_nondegeneratePieces.mp hP).1 (mem_nondegeneratePieces.mp hP).2)
    (isClosedChain_nondegeneratePieces hclosed) (isPreconnected_compl_closedSquare a r)
    _ (not_mem_closedSquare_of_dist_gt hx) (not_mem_closedSquare_of_dist_gt hy)
  intro z hz hzL
  apply hz
  exact (Plane.supNorm_le_norm (z - a)).trans
    (by simpa only [dist_eq_norm] using hL z (cover_nondegeneratePieces_subset L hzL))

end Reeken.Geometry
