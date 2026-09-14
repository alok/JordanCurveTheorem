import Reeken.Geometry.AnnulusOverlay
import Reeken.Geometry.SpokeSeparation
import Reeken.Nonstandard.InnerSpokeCell

/-! # An actual internal drawing of the ring between the two polygons

The chosen standard point rules out collapse of all nearest feet to one point.
Two disjoint connections therefore exist. They ensure that the ring drawing is
2-connected, allowing the finite face-cycle theorem to be applied to its domains.
-/

open Filter Set Schoenflies Reeken.Geometry
open scoped Graph

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)

include hmax

theorem eventually_disjoint_corner_connections
    (q : ℕ → Σ m, ClosedPolygon m) (foot : ℕ → Plane → Plane)
    {A : Plane} (hAC : A ∉ f '' Icc 0 1)
    (hA : ∀ᶠ i in hyperfilter ℕ, A ∈ inside (q i).2.carrier)
    (hfoot : ∀ᶠ i in hyperfilter ℕ, ∀ x, IsNearest (p i).trace x (foot i x))
    (hshort : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ j : ZMod ((q i).1 + 3),
      dist ((q i).2.vertex j) (foot i ((q i).2.vertex j)) < η) :
    ∀ᶠ i in hyperfilter ℕ, ∃ j : ZMod ((q i).1 + 3),
      Disjoint (segment ℝ ((q i).2.vertex j) (foot i ((q i).2.vertex j)))
        (segment ℝ ((q i).2.vertex 0) (foot i ((q i).2.vertex 0))) := by
  have hAsh : A ∉ shadow (fun i ↦ (p i).trace) := by rwa [shadow_polygon p hmax]
  obtain ⟨δ, hδ, hd⟩ := (not_mem_shadow_iff _ A).mp hAsh
  filter_upwards [hA, hfoot, hd, hshort (δ / 4) (by positivity)] with i hAi hfi hdi hsi
  have hsqrt : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hbound : Real.sqrt 2 * (δ / 4) ≤ 2 * (δ / 4) :=
    mul_le_mul_of_nonneg_right hsqrt (by positivity)
  obtain ⟨j, _, hj⟩ := exists_disjoint_corner_connections (q i).2 hfi hAi
    (fun y hy ↦ by simpa only [dist_comm] using hdi y hy) (by linarith) (fun j ↦ (hsi j).le)
  exact ⟨j, hj⟩

/-- Both polygons and all chosen corner connections are actual internal data.
The ring domains have yet to be identified as the three-part barriers in the paper. -/
theorem exists_internal_annulus_drawing (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)
    {A : Plane} (hA : A ∈ standardInside p) :
    ∃ q : ℕ → Σ m, ClosedPolygon m, ∃ foot : ℕ → Plane → Plane, ∃ points : ℕ → List Plane,
      A ∈ deep (fun i ↦ inside (q i).2.carrier) ∧
      shadow (fun i ↦ (q i).2.carrier) ⊆ f '' Icc 0 1 ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ j : ZMod ((q i).1 + 3),
        dist ((q i).2.vertex j) (foot i ((q i).2.vertex j)) < η) ∧
      ∀ᶠ i in hyperfilter ℕ,
        let G := overlayGraph ((p i).annulusPieces (q i).2 (foot i)) (points i)
        A ∈ inside (q i).2.carrier ∧ (q i).2.carrier ⊆ inside (p i).trace ∧
        inside (q i).2.carrier ⊆ inside (p i).trace ∧
        closure (inside (q i).2.carrier) ⊆ (f '' Icc 0 1)ᶜ ∧
        (∀ x, IsNearest (p i).trace x (foot i x)) ∧
        (∀ j : ZMod ((q i).1 + 3),
          Disjoint (segment ℝ ((q i).2.vertex j) (foot i ((q i).2.vertex j)))
            (inside (q i).2.carrier)) ∧
        Graph.IsDrawing G segmentDrawing ∧ G.IsTwoConnected ∧
        Graph.pointSet G segmentDrawing =
          ((p i).trace ∪ (q i).2.carrier) ∪
            ⋃ j, segment ℝ ((q i).2.vertex j) (foot i ((q i).2.vertex j)) := by
  obtain ⟨q, foot, hq, hshort, hshadow, hdeep, _⟩ := exists_internal_inner_spoke_cell p hmax hs hA
  have hAC : A ∉ f '' Icc 0 1 := by
    have h : A ∈ standardInside p ∪ standardOutside p := Or.inl hA
    rwa [standardRegions_union p hmax hs] at h
  have hdis := eventually_disjoint_corner_connections p hmax q foot hAC
    (hq.mono fun _ hi ↦ hi.1) (hq.mono fun _ hi ↦ hi.2.2.2.2.1) hshort
  let valid (i : ℕ) (points : List Plane) : Prop :=
    let G := overlayGraph ((p i).annulusPieces (q i).2 (foot i)) points
    Graph.IsDrawing G segmentDrawing ∧ G.IsTwoConnected ∧
    Graph.pointSet G segmentDrawing = ((p i).trace ∪ (q i).2.carrier) ∪
      ⋃ j, segment ℝ ((q i).2.vertex j) (foot i ((q i).2.vertex j))
  have hex : ∀ᶠ i in hyperfilter ℕ, ∃ points, valid i points := by
    filter_upwards [hq, hs, vertex_count_unlimited p hmax 2, hdis] with i hi hsi hni hdi
    obtain ⟨j, hj⟩ := hdi
    obtain ⟨points, hd, htwo, hpoint, _, _⟩ := hsi.exists_annulus_overlay (p i) (by omega)
      (q i).2 (foot i) (fun j ↦ (hi.2.2.2.2.1 _).1) hj
    exact ⟨points, hd, htwo, hpoint⟩
  obtain ⟨points, hpoints⟩ := (exists_holds (U := hyperfilter ℕ) valid).mpr hex
  star_cases points
  refine ⟨q, foot, points, hdeep, hshadow, hshort, ?_⟩
  filter_upwards [hq, hpoints] with i hi hpi
  exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1,
    fun j ↦ (hi.2.2.2.2.2 j).1, hpi⟩

end Reeken.NSA
