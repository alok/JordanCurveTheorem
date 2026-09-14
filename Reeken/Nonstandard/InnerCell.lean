import Reeken.Geometry.RectangleCells
import Reeken.Nonstandard.RectangleApproximation
import Reeken.Nonstandard.CommonBoundary

/-! # An internal inner polygon around a prescribed standard interior point

The actual rectangle arrangement gives a simple internal polygon lying in the
original polygon's inside, with the chosen point deeply inside. Its closed
interior avoids the extended curve and its boundary lies in the curve's monad.
This is the construction part of Lemma 3; it does not yet assert that every
standard interior point belongs to this same cell.
-/

open Filter Set Metric Topology
open Reeken.Geometry Schoenflies

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)

include hmax

/-- The thin rectangles cannot contain both of two fixed separated standard cut vertices. -/
theorem exists_vertices_beyond_rectangle_scale {ε : ℕ → ℝ}
    (hε : Near (ofSeq (U := hyperfilter ℕ) ε) (std 0)) :
    ∃ a b : (i : ℕ) → Fin ((p i).n + 1),
      ∀ᶠ i in hyperfilter ℕ, 2 * ((p i).maxEdge + 4 * ε i) <
        dist ((p i).vertex (a i)) ((p i).vertex (b i)) := by
  have hf : f 0 ≠ f (1 / 2) := by
    intro h
    have he := f.injectiveOn (x₁ := 0) (x₂ := 1 / 2) (by norm_num) (by norm_num) h
    norm_num at he
  let d := dist (f 0) (f (1 / 2))
  have hd : 0 < d := dist_pos.mpr hf
  obtain ⟨a, b, ha, hb, _⟩ := exists_ordered_cut_vertices p hmax
    (A := 0) (B := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hva := (near_std_iff_tendsto _ _).mp (cut_vertex_near p a ha)
  have hvb := (near_std_iff_tendsto _ _).mp (cut_vertex_near p b hb)
  have hdist : ∀ᶠ i in hyperfilter ℕ,
      d / 2 < dist ((p i).vertex (a i)) ((p i).vertex (b i)) :=
    (hva.dist hvb) (Ioi_mem_nhds (by change d / 2 < d; linarith))
  refine ⟨a, b, ?_⟩
  filter_upwards [hdist, rectangle_error_small p hmax hε (show 0 < d / 4 by positivity)] with i hi herr
  linarith

theorem exists_internal_inner_cell (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)
    {A : Plane} (hA : A ∈ standardInside p) :
    ∃ q : ℕ → Σ m, ClosedPolygon m,
      (∀ᶠ i in hyperfilter ℕ,
        A ∈ inside (q i).2.carrier ∧ (q i).2.carrier ⊆ inside (p i).trace ∧
        inside (q i).2.carrier ⊆ inside (p i).trace ∧
        closure (inside (q i).2.carrier) ⊆ (f '' Icc 0 1)ᶜ) ∧
      shadow (fun i ↦ (q i).2.carrier) ⊆ f '' Icc 0 1 ∧
      A ∈ deep (fun i ↦ inside (q i).2.carrier) := by
  have hAC : A ∉ f '' Icc 0 1 := by
    have h : A ∈ standardInside p ∪ standardOutside p := Or.inl hA
    rwa [standardRegions_union p hmax hs] at h
  obtain ⟨ε, hε, hcover, hshadow⟩ := exists_infinitesimal_rectangle_cover p hmax
  obtain ⟨a, b, hfar⟩ := exists_vertices_beyond_rectangle_scale p hmax hε
  have havoid : ∀ᶠ i in hyperfilter ℕ, A ∉ (p i).rectangleCover (ε i) := by
    have hdis : Disjoint {A} (f '' Icc 0 1) := Set.disjoint_left.mpr fun x hx hxc ↦
      hAC ((mem_singleton_iff.mp hx) ▸ hxc)
    exact (eventually_disjoint_innerConstructionZone p hmax hε isCompact_singleton hdis).mono
      fun _ hi hmem ↦ Set.disjoint_left.mp hi rfl (Or.inl hmem)
  have hex : ∀ᶠ i in hyperfilter ℕ, ∃ Q : Σ m, ClosedPolygon m,
      A ∈ inside Q.2.carrier ∧ Q.2.carrier ⊆ inside (p i).trace ∧
      inside Q.2.carrier ⊆ inside (p i).trace ∧
      closure (inside Q.2.carrier) ⊆ (f '' Icc 0 1)ᶜ ∧
      Q.2.carrier ⊆ (p i).rectangleCover (ε i) := by
    filter_upwards [hs, vertex_count_unlimited p hmax 2, hcover, hfar, havoid,
      eventually_mem_of_mem_deep hA] with i hsi hni hci hfi hai hAi
    obtain ⟨m, Q, hAQ, hQi, hQQi, hQcl, hQboundary⟩ :=
      hsi.exists_rectangle_cell (p i) (by omega) hci.1 hfi hAi hai
    refine ⟨⟨m, Q⟩, hAQ, hQi, hQQi, ?_, ?_⟩
    · exact fun x hx hxc ↦ hQcl hx (hci.2 hxc)
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hQboundary hx)
      exact mem_iUnion.mpr ⟨j, (isClosed_closedEdgeRectangle _ _ _ _).frontier_subset hj⟩
  have : Nonempty (Σ m, ClosedPolygon m) := ⟨⟨1, squarePolygon 0 (r := 1) zero_lt_one⟩⟩
  obtain ⟨q, hq⟩ := (exists_holds (U := hyperfilter ℕ) (fun i (Q : Σ m, ClosedPolygon m) ↦
    A ∈ inside Q.2.carrier ∧ Q.2.carrier ⊆ inside (p i).trace ∧
    inside Q.2.carrier ⊆ inside (p i).trace ∧
    closure (inside Q.2.carrier) ⊆ (f '' Icc 0 1)ᶜ ∧
    Q.2.carrier ⊆ (p i).rectangleCover (ε i))).mpr hex
  star_cases q
  have hqshadow : shadow (fun i ↦ (q i).2.carrier) ⊆ f '' Icc 0 1 :=
    (shadow_mono (hq.mono fun _ hi x hx ↦ Or.inl (hi.2.2.2.2 hx))).trans hshadow
  refine ⟨q, hq.mono (fun _ hi ↦ ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩), hqshadow, ?_⟩
  apply mem_deep_of_separation (b := fun i ↦ (q i).2.carrier)
    (v := fun i ↦ outside (q i).2.carrier) _ (hq.mono fun _ hi ↦ hi.1)
    (fun h ↦ hAC (hqshadow h))
  exact Eventually.of_forall fun i ↦ ⟨(q i).2.isSeparating_carrier.isOpen_inside,
    (q i).2.isSeparating_carrier.isOpen_outside, disjoint_inside_outside, inside_union_outside _⟩

end Reeken.NSA
