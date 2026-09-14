import Reeken.Geometry.SpokeCell
import Reeken.Nonstandard.InnerCell

/-! # The internal inner cell with infinitesimal shortest connections

This constructs the cell used in Lemma 3 from the rectangle-and-connection
arrangement. Every corner has a shortest connection to the outer polygon,
uniformly infinitesimal and disjoint from the inner cell's interior. The later
ring argument must still show that the chosen cell contains every standard
interior point, rather than only the prescribed point.
-/

open Filter Set Metric Topology
open Reeken.Geometry Schoenflies

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)

include hmax

theorem exists_internal_inner_spoke_cell (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)
    {A : Plane} (hA : A ∈ standardInside p) :
    ∃ q : ℕ → Σ m, ClosedPolygon m, ∃ foot : ℕ → Plane → Plane,
      (∀ᶠ i in hyperfilter ℕ,
        A ∈ inside (q i).2.carrier ∧ (q i).2.carrier ⊆ inside (p i).trace ∧
        inside (q i).2.carrier ⊆ inside (p i).trace ∧
        closure (inside (q i).2.carrier) ⊆ (f '' Icc 0 1)ᶜ ∧
        (∀ x, IsNearest (p i).trace x (foot i x)) ∧
        ∀ j : ZMod ((q i).1 + 3),
          Disjoint (segment ℝ ((q i).2.vertex j) (foot i ((q i).2.vertex j)))
            (inside (q i).2.carrier) ∧
          segment ℝ ((q i).2.vertex j) (foot i ((q i).2.vertex j)) \
            {foot i ((q i).2.vertex j)} ⊆ inside (p i).trace) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ j : ZMod ((q i).1 + 3),
        dist ((q i).2.vertex j) (foot i ((q i).2.vertex j)) < η) ∧
      shadow (fun i ↦ (q i).2.carrier) ⊆ f '' Icc 0 1 ∧
      A ∈ deep (fun i ↦ inside (q i).2.carrier) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ (q i).2.carrier,
        ∃ y ∈ (p i).trace, dist x y < η) := by
  have hAC : A ∉ f '' Icc 0 1 := by
    have h : A ∈ standardInside p ∪ standardOutside p := Or.inl hA
    rwa [standardRegions_union p hmax hs] at h
  obtain ⟨ε, hε, hcover, hshadow⟩ := exists_infinitesimal_rectangle_cover p hmax
  obtain ⟨a, b, hfar⟩ := exists_vertices_beyond_rectangle_scale p hmax hε
  have havoid : ∀ᶠ i in hyperfilter ℕ,
      A ∉ (p i).rectangleCover (ε i) ∪ (p i).nearestConnectorCover (ε i) := by
    have hdis : Disjoint {A} (f '' Icc 0 1) := Set.disjoint_left.mpr fun x hx hxc ↦
      hAC ((mem_singleton_iff.mp hx) ▸ hxc)
    exact (eventually_disjoint_innerConstructionZone p hmax hε isCompact_singleton hdis).mono
      fun _ hi hmem ↦ Set.disjoint_left.mp hi rfl hmem
  let Data := (Σ m, ClosedPolygon m) × (Plane → Plane)
  let valid : ℕ → Data → Prop := fun i d ↦
    A ∈ inside d.1.2.carrier ∧ d.1.2.carrier ⊆ inside (p i).trace ∧
    inside d.1.2.carrier ⊆ inside (p i).trace ∧
    closure (inside d.1.2.carrier) ⊆ (f '' Icc 0 1)ᶜ ∧
    d.1.2.carrier ⊆ innerConstructionZone p ε i ∧
    (∀ x, IsNearest (p i).trace x (d.2 x)) ∧
    ∀ j : ZMod (d.1.1 + 3),
      Disjoint (segment ℝ (d.1.2.vertex j) (d.2 (d.1.2.vertex j))) (inside d.1.2.carrier) ∧
      segment ℝ (d.1.2.vertex j) (d.2 (d.1.2.vertex j)) \ {d.2 (d.1.2.vertex j)} ⊆
        inside (p i).trace ∧
      dist (d.1.2.vertex j) (d.2 (d.1.2.vertex j)) ≤ (p i).maxEdge + 4 * ε i
  have hex : ∀ᶠ i in hyperfilter ℕ, ∃ d : Data, valid i d := by
    filter_upwards [hs, vertex_count_unlimited p hmax 2, hcover, hfar, havoid,
      eventually_mem_of_mem_deep hA] with i hsi hni hci hfi hai hAi
    obtain ⟨m, Q, foot, hAQ, hQi, hQQi, hQcl, hQzone, hf, hspoke⟩ :=
      hsi.exists_rectangle_spoke_cell (p i) (by omega) hci.1 hfi hAi hai
    exact ⟨(⟨m, Q⟩, foot), hAQ, hQi, hQQi,
      fun x hx hxc ↦ hQcl hx (hci.2 hxc), hQzone, hf, hspoke⟩
  have : Nonempty Data := ⟨(⟨1, squarePolygon 0 (r := 1) zero_lt_one⟩, id)⟩
  obtain ⟨d, hd⟩ := (exists_holds (U := hyperfilter ℕ) valid).mpr hex
  star_cases d
  have hqshadow : shadow (fun i ↦ (d i).1.2.carrier) ⊆ f '' Icc 0 1 :=
    (shadow_mono (hd.mono fun _ hi ↦ hi.2.2.2.2.1)).trans hshadow
  refine ⟨fun i ↦ (d i).1, fun i ↦ (d i).2, ?_, ?_, hqshadow, ?_, ?_⟩
  · exact hd.mono fun _ hi ↦ ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1,
      hi.2.2.2.2.2.1, fun j ↦ ⟨(hi.2.2.2.2.2.2 j).1, (hi.2.2.2.2.2.2 j).2.1⟩⟩
  · intro η hη
    filter_upwards [hd, rectangle_error_small p hmax hε hη] with i hi herr
    exact fun j ↦ ((hi.2.2.2.2.2.2 j).2.2).trans_lt herr
  · apply mem_deep_of_separation (b := fun i ↦ (d i).1.2.carrier)
      (v := fun i ↦ outside (d i).1.2.carrier) _ (hd.mono fun _ hi ↦ hi.1)
      (fun h ↦ hAC (hqshadow h))
    exact Eventually.of_forall fun i ↦ ⟨(d i).1.2.isSeparating_carrier.isOpen_inside,
      (d i).1.2.isSeparating_carrier.isOpen_outside, disjoint_inside_outside, inside_union_outside _⟩
  · intro η hη
    filter_upwards [hd, rectangle_error_small p hmax hε hη, vertex_count_unlimited p hmax 1]
      with i hi herr hni
    intro x hx
    have hxzone := hi.2.2.2.2.1 hx
    obtain ⟨y, hy, hxy⟩ := hxzone.elim
      ((p i).rectangleCover_near_trace (by omega)) ((p i).nearestConnectorCover_near_trace (by omega))
    exact ⟨y, hy, hxy.trans_lt herr⟩

end Reeken.NSA
