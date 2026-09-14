import Reeken.Nonstandard.RingContainment

/-! # Infinitesimal barriers on the outside

The same cancellation proof compares two standard outside points.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

theorem mem_deep_outer_of_near_boundary (q : ℕ → Σ m, ClosedPolygon m)
    (hnear : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ (q i).2.carrier,
      ∃ y ∈ (p i).trace, dist x y < η)
    {A B : Plane} (hA : A ∈ standardOutside p) (hB : B ∈ standardOutside p)
    (hAq : ∀ᶠ i in hyperfilter ℕ, A ∈ outside (q i).2.carrier) :
    B ∈ deep (fun i ↦ outside (q i).2.carrier) := by
  classical
  have hoff : ∀ x ∈ standardOutside p, x ∉ f '' Icc 0 1 := by
    intro x hx
    have h : x ∈ standardInside p ∪ standardOutside p := Or.inr hx
    rwa [standardRegions_union p hmax hs] at h
  have hAsh : A ∉ shadow (fun i ↦ (p i).trace) := by
    rw [shadow_polygon p hmax]
    exact hoff A hA
  have hBsh : B ∉ shadow (fun i ↦ (p i).trace) := by
    rw [shadow_polygon p hmax]
    exact hoff B hB
  obtain ⟨δA, hδA, hdA⟩ := (not_mem_shadow_iff _ A).mp hAsh
  obtain ⟨δB, hδB, hdB⟩ := (not_mem_shadow_iff _ B).mp hBsh
  let δ := min δA δB
  have hδ : 0 < δ := lt_min hδA hδB
  have hqshadow : shadow (fun i ↦ (q i).2.carrier) ⊆ f '' Icc 0 1 := by
    rw [← shadow_polygon p hmax]
    exact shadow_subset_of_approximation hnear
  have hBQsh : B ∉ shadow (fun i ↦ (q i).2.carrier) := fun h ↦ hoff B hB (hqshadow h)
  have hBoff : ∀ᶠ i in hyperfilter ℕ, B ∉ (q i).2.carrier := by
    apply Ultrafilter.eventually_not.mpr
    intro h
    exact hBQsh ⟨std B, h, Near.refl _⟩
  obtain ⟨L, hL, hedge⟩ := exists_internal_fine_chain q
  have hnearL : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ cover (L i),
      ∃ y ∈ (p i).trace, dist x y < η := by
    intro η hη
    exact (hnear η hη).mono fun i hi x hx ↦ hi x ((hL i).1 ▸ hx)
  have hbarriers := vertexBarriers_uniformly_small p hmax hs L hnearL hedge
  have hBq : ∀ᶠ i in hyperfilter ℕ, B ∈ outside (q i).2.carrier := by
    filter_upwards [hs, vertex_count_unlimited p hmax 2, hAq, hBoff, hdA, hdB,
      eventually_mem_of_mem_deep hA, eventually_mem_of_mem_deep hB,
      hbarriers (δ / 4) (by positivity)] with i hsi hni hAqi hBoi hAi hBi hApi hBpi hbar
    have hn : 2 ≤ (p i).n := by omega
    let allPieces := (q i).2.pieces ++
      (L i ++ ((L i).flatMap (p i).vertexArc ++ (L i).flatMap (p i).vertexBarrier))
    obtain ⟨u, hu, hdir⟩ := exists_direction_nondegenerate allPieces
    have hdirQ : ∀ P ∈ (q i).2.pieces, hgt u P.1 ≠ hgt u P.2 := by
      intro P hP
      exact hdir P (List.mem_append_left _ hP) ((q i).2.pieces_nondeg P hP)
    have hdirArc : ∀ P ∈ (L i).flatMap (p i).vertexArc,
        P.Nondeg → hgt u P.1 ≠ hgt u P.2 := by
      intro P hP
      apply hdir P
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hP))
    have hlocal : ∀ P ∈ L i,
        parity u ((p i).vertexBarrier P) A = parity u ((p i).vertexBarrier P) B := by
      intro P hP
      have hdirBarrier : ∀ R ∈ (p i).vertexBarrier P, R.Nondeg → hgt u R.1 ≠ hgt u R.2 := by
        intro R hR
        apply hdir R
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨P, hP, hR⟩)))
      have hcenter : (p i).vertexProjection P.1 ∈ (p i).trace := (p i).vertexProjection_mem_trace _
      have hclearA : δ ≤ dist A ((p i).vertexProjection P.1) := by
        rw [dist_comm]
        exact (min_le_left _ _).trans (hAi _ hcenter)
      have hclearB : δ ≤ dist B ((p i).vertexProjection P.1) := by
        rw [dist_comm]
        exact (min_le_right _ _).trans (hBi _ hcenter)
      have hsqrt : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
      have hscale : Real.sqrt 2 * (δ / 4) < δ := by
        have h := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ δ / 4 by positivity)
        linarith
      exact parity_eq_far_from_small_chain (isClosedChain_edgeBarrier ((p i).vertexArc_chain hn hsi P))
        hu hdirBarrier (fun z hz ↦ (hbar P hP z hz).le) (hscale.trans_le hclearA)
        (hscale.trans_le hclearB)
    have hparity : parity u (L i) A = parity u (L i) B :=
      parity_eq_outside_of_edge_barriers (hL i).2.1 (p i).vertexProjection (p i).vertexArc
        (fun P _ ↦ (p i).vertexArc_chain hn hsi P) (hsi.isSeparating hn)
        (fun P _ ↦ (p i).vertexArc_subset_trace P) hu hdirArc hApi hBpi hlocal
    rw [(hL i).2.2.2 u hdirQ A, (hL i).2.2.2 u hdirQ B] at hparity
    have hzero : parity u (q i).2.pieces B = 0 := by
      rw [← hparity]
      exact (q i).2.parity_eq_zero_of_mem_outside hu hdirQ hAqi
    have hregions : B ∈ inside (q i).2.carrier ∪ outside (q i).2.carrier := by
      rw [inside_union_outside]
      exact hBoi
    exact hregions.resolve_left fun hin ↦ zero_ne_one
      (hzero.symm.trans ((q i).2.parity_eq_one_of_mem_inside hu hdirQ hin))
  apply mem_deep_of_separation (b := fun i ↦ (q i).2.carrier)
    (v := fun i ↦ inside (q i).2.carrier) _ hBq hBQsh
  exact Eventually.of_forall fun i ↦ ⟨(q i).2.isSeparating_carrier.isOpen_outside,
    (q i).2.isSeparating_carrier.isOpen_inside, disjoint_inside_outside.symm,
    (union_comm _ _).trans (inside_union_outside _)⟩

end Reeken.NSA
