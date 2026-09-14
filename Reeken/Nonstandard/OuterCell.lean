import Reeken.Geometry.OuterCells
import Reeken.Nonstandard.InnerCell

/-! # An internal outer polygon

Transfer the unbounded rectangle face. Its closed outside misses the extended
curve and its boundary is uniformly infinitesimally close to the inscribed polygon.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

theorem exists_internal_outer_cell :
    ∃ q : ℕ → Σ m, ClosedPolygon m,
      (∀ᶠ i in hyperfilter ℕ,
        (q i).2.carrier ⊆ outside (p i).trace ∧ outside (q i).2.carrier ⊆ outside (p i).trace ∧
        closure (outside (q i).2.carrier) ⊆ (f '' Icc 0 1)ᶜ) ∧
      shadow (fun i ↦ (q i).2.carrier) ⊆ f '' Icc 0 1 ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ (q i).2.carrier,
        ∃ y ∈ (p i).trace, dist x y < η) := by
  obtain ⟨ε, hε, hcover, hshadow⟩ := exists_infinitesimal_rectangle_cover p hmax
  obtain ⟨a, b, hfar⟩ := exists_vertices_beyond_rectangle_scale p hmax hε
  have hex : ∀ᶠ i in hyperfilter ℕ, ∃ Q : Σ m, ClosedPolygon m,
      Q.2.carrier ⊆ outside (p i).trace ∧ outside Q.2.carrier ⊆ outside (p i).trace ∧
      closure (outside Q.2.carrier) ⊆ (f '' Icc 0 1)ᶜ ∧
      Q.2.carrier ⊆ (p i).rectangleCover (ε i) := by
    filter_upwards [hs, vertex_count_unlimited p hmax 2, hcover, hfar] with i hsi hni hci hfi
    obtain ⟨m, Q, hQout, hout, hcl, hQsub⟩ :=
      hsi.exists_rectangle_outer_cell (p i) (by omega) hci.1 hfi
    exact ⟨⟨m, Q⟩, hQout, hout, fun x hx hxc ↦ hcl hx (hci.2 hxc), hQsub⟩
  have : Nonempty (Σ m, ClosedPolygon m) := ⟨⟨1, squarePolygon 0 (r := 1) zero_lt_one⟩⟩
  obtain ⟨q, hq⟩ := (exists_holds (U := hyperfilter ℕ) (fun i (Q : Σ m, ClosedPolygon m) ↦
    Q.2.carrier ⊆ outside (p i).trace ∧ outside Q.2.carrier ⊆ outside (p i).trace ∧
    closure (outside Q.2.carrier) ⊆ (f '' Icc 0 1)ᶜ ∧
    Q.2.carrier ⊆ (p i).rectangleCover (ε i))).mpr hex
  star_cases q
  refine ⟨q, hq.mono (fun _ hi ↦ ⟨hi.1, hi.2.1, hi.2.2.1⟩), ?_, ?_⟩
  · exact (shadow_mono (hq.mono fun _ hi x hx ↦ Or.inl (hi.2.2.2 hx))).trans hshadow
  · intro η hη
    filter_upwards [hq, vertex_count_unlimited p hmax 1, rectangle_error_small p hmax hε hη]
      with i hi hni herr
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (p i).rectangleCover_near_trace (by omega) (hi.2.2.2 hx)
    exact ⟨y, hy, hxy.trans_lt herr⟩

end Reeken.NSA
