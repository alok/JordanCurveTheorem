import Reeken.Geometry.SquareConnector
import Reeken.Nonstandard.BoundaryConnector
import Reeken.Nonstandard.PolygonSquares
import Reeken.Nonstandard.CutVertices
import Reeken.Nonstandard.StandardRegions

/-! # The common boundary of the standard interior and exterior

This is the conclusion of Section 3 of Kanovei–Reeken. Actual clipped polygonal
cells supply connectors on arbitrarily small square boundaries. The two long
arcs have disjoint shadows on a fixed annulus, so a balanced connector point
has positive standard distance from the polygon. Its standard part is deep
on the chosen side and lies in the prescribed neighborhood of the curve.
-/

open Filter Set Metric Topology
open Reeken.Geometry Schoenflies

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < ε)
  (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)

include hmax hs

/-- Every neighborhood of a curve point meets either chosen standard side. -/
theorem ball_inter_deep_nonempty {u v : ℕ → Set Plane}
    (hregions : ∀ᶠ i in hyperfilter ℕ, IsRegionPair (p i).trace (u i) (v i))
    {A : ℝ} (hA : A ∈ Ico 0 1) {ε : ℝ} (hε : 0 < ε) :
    (ball (f A) ε ∩ deep u).Nonempty := by
  let B := (A + 1) / 2
  have hAB : A < B := by dsimp [B]; linarith [hA.2]
  have hB : B ∈ Ico (0 : ℝ) 1 := by dsimp [B]; constructor <;> linarith [hA.1, hA.2]
  have hfAB : f A ≠ f B := fun h ↦ hAB.ne (f.injectiveOn hA hB h)
  obtain ⟨a, b, ha, hb, hab⟩ := exists_ordered_cut_vertices p hmax
    (Ico_subset_Icc_self hA) (Ico_subset_Icc_self hB) hAB
  obtain ⟨r, hr, hfar, hball⟩ := exists_small_square_scale hfAB hε
  obtain ⟨ρ, hρ, _, hann, hop⟩ := exists_generic_polygon_squares p a b ha hb hr hfar
  let K := squareAnnulus (f A) r (2 * r)
  have hdis : Disjoint K (shadow (fun i ↦ (p i).forwardArc (a i) (b i)) ∩
      shadow (fun i ↦ (p i).backwardArc (a i) (b i))) :=
    (squareAnnulus_disjoint_endpoints hr hfar).mono_right
      (common_arc_shadow_subset p a b hmax (hab.mono fun _ h ↦ h.le) ha hb)
  have hex : ∀ᶠ i in hyperfilter ℕ, ∃ T : Set Plane,
      IsPreconnected T ∧ T ⊆ K ∧
      (T ∩ (p i).forwardArc (a i) (b i)).Nonempty ∧
      (T ∩ (p i).backwardArc (a i) (b i)).Nonempty ∧
      T \ ((p i).forwardArc (a i) (b i) ∪ (p i).backwardArc (a i) (b i)) ⊆ u i := by
    filter_upwards [hs, vertex_count_unlimited p hmax 2, hab, hop, hregions] with i hsi hni habi hopi hreg
    obtain ⟨T, hT, hTS, hTF, hTB, hTu⟩ := hsi.exists_square_connector (p i)
      (by omega) habi (hr.trans (hρ i).1) hopi.1 hopi.2 hreg.left
    exact ⟨T, hT, hTS.trans (hann i), hTF, hTB, by simpa only [(p i).arcs_union] using hTu⟩
  obtain ⟨c, hc⟩ := (exists_holds (U := hyperfilter ℕ) (fun i (T : Set Plane) ↦
    IsPreconnected T ∧ T ⊆ K ∧
    (T ∩ (p i).forwardArc (a i) (b i)).Nonempty ∧
    (T ∩ (p i).backwardArc (a i) (b i)).Nonempty ∧
    T \ ((p i).forwardArc (a i) (b i) ∪ (p i).backwardArc (a i) (b i)) ⊆ u i)).mpr hex
  obtain ⟨c, rfl⟩ := ofSeq_surjective c
  have hcompact : ∀ᶠ i in hyperfilter ℕ,
      IsCompact ((p i).forwardArc (a i) (b i)) ∧ ((p i).forwardArc (a i) (b i)).Nonempty ∧
      IsCompact ((p i).backwardArc (a i) (b i)) ∧ ((p i).backwardArc (a i) (b i)).Nonempty :=
    Eventually.of_forall fun i ↦ ⟨(p i).isCompact_forwardArc (a i) (b i),
      (p i).forwardArc_nonempty (a i) (b i), (p i).isCompact_backwardArc (a i) (b i),
      (p i).backwardArc_nonempty (a i) (b i)⟩
  have hsep : ∀ᶠ i in hyperfilter ℕ,
      IsOpen (u i) ∧ IsOpen (v i) ∧ Disjoint (u i) (v i) ∧
      u i ∪ v i = ((p i).forwardArc (a i) (b i) ∪ (p i).backwardArc (a i) (b i))ᶜ := by
    filter_upwards [eventually_polygon_separates p hmax hs, hregions] with i hi hreg
    exact ⟨hreg.left.isOpen hi, hreg.right.isOpen hi, hreg.disjoint,
      by simpa only [(p i).arcs_union] using hreg.union_eq⟩
  obtain ⟨x, hxK, hx⟩ := exists_deep_point_of_connectors
    (isCompact_squareAnnulus (f A) r (2 * r)) hdis hcompact hsep hc
  exact ⟨x, hball hxK.1, hx⟩

theorem curve_subset_closure_deep {u v : ℕ → Set Plane}
    (hregions : ∀ᶠ i in hyperfilter ℕ, IsRegionPair (p i).trace (u i) (v i)) :
    f '' Icc 0 1 ⊆ closure (deep u) := by
  have hparam : ∀ A ∈ Ico (0 : ℝ) 1, f A ∈ closure (deep u) := by
    intro A hA
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨x, hxball, hx⟩ := ball_inter_deep_nonempty p hmax hs hregions hA hε
    exact ⟨x, hx, by simpa only [mem_ball, dist_comm] using hxball⟩
  rintro x ⟨A, hA, rfl⟩
  by_cases hA1 : A = 1
  · rw [hA1, f.endpoint]
    exact hparam 0 ⟨le_rfl, zero_lt_one⟩
  · exact hparam A ⟨hA.1, lt_of_le_of_ne hA.2 hA1⟩

theorem curve_subset_closure_standardInside :
    f '' Icc 0 1 ⊆ closure (standardInside p) :=
  curve_subset_closure_deep p hmax hs
    (Eventually.of_forall fun _ ↦ Or.inl ⟨rfl, rfl⟩)

theorem curve_subset_closure_standardOutside :
    f '' Icc 0 1 ⊆ closure (standardOutside p) :=
  curve_subset_closure_deep p hmax hs
    (Eventually.of_forall fun _ ↦ Or.inr ⟨rfl, rfl⟩)

/-- Both open sides have the original curve as their whole boundary. -/
theorem frontier_standardInside : frontier (standardInside p) = f '' Icc 0 1 := by
  rw [(isOpen_standardInside p).frontier_eq]
  apply Subset.antisymm
  · intro x hx
    by_contra hxc
    have hxunion : x ∈ standardInside p ∪ standardOutside p := by
      rw [standardRegions_union p hmax hs]
      exact hxc
    rcases hxunion with hxi | hxo
    · exact hx.2 hxi
    · exact Set.disjoint_left.mp
        ((disjoint_standardRegions p).closure_left (isOpen_standardOutside p)) hx.1 hxo
  · intro x hxc
    refine ⟨curve_subset_closure_standardInside p hmax hs hxc, ?_⟩
    intro hxi
    have hxunion : x ∈ standardInside p ∪ standardOutside p := Or.inl hxi
    rw [standardRegions_union p hmax hs] at hxunion
    exact hxunion hxc

theorem frontier_standardOutside : frontier (standardOutside p) = f '' Icc 0 1 := by
  rw [(isOpen_standardOutside p).frontier_eq]
  apply Subset.antisymm
  · intro x hx
    by_contra hxc
    have hxunion : x ∈ standardInside p ∪ standardOutside p := by
      rw [standardRegions_union p hmax hs]
      exact hxc
    rcases hxunion with hxi | hxo
    · exact Set.disjoint_left.mp
        ((disjoint_standardRegions p).symm.closure_left (isOpen_standardInside p)) hx.1 hxi
    · exact hx.2 hxo
  · intro x hxc
    refine ⟨curve_subset_closure_standardOutside p hmax hs hxc, ?_⟩
    intro hxo
    have hxunion : x ∈ standardInside p ∪ standardOutside p := Or.inr hxo
    rw [standardRegions_union p hmax hs] at hxunion
    exact hxunion hxc

theorem standardInside_nonempty : (standardInside p).Nonempty := by
  obtain ⟨x, _, hx⟩ := ball_inter_deep_nonempty p hmax hs
    (Eventually.of_forall fun _ ↦ Or.inl ⟨rfl, rfl⟩)
    (A := 0) ⟨le_rfl, zero_lt_one⟩ (ε := 1) zero_lt_one
  exact ⟨x, hx⟩

end Reeken.NSA
