import Reeken.Geometry.TriangleCoordinates

/-! # Overlapping segments on a line

A segment whose ends avoid the open base, but whose interior meets it, contains
the whole base whenever its ends lie on the base's line.
-/

open Set Schoenflies

namespace Reeken.Geometry

theorem unit_segment_subset_of_meets_of_ends_outside {u v w : ℝ}
    (hw : w ∈ Ioo (0 : ℝ) 1) (hwuv : w ∈ openSegment ℝ u v)
    (hu : u ∉ Ioo (0 : ℝ) 1) (hv : v ∉ Ioo (0 : ℝ) 1) :
    Icc (0 : ℝ) 1 ⊆ segment ℝ u v := by
  have huv : u ≠ v := by
    rintro rfl
    rw [openSegment_same, mem_singleton_iff] at hwuv
    exact hu (hwuv ▸ hw)
  rw [openSegment_eq_Ioo' huv] at hwuv
  rw [segment_eq_uIcc]
  have hmin : min u v ≤ 0 := by
    by_contra h
    have h0 : 0 < min u v := lt_of_not_ge h
    rcases le_total u v with huv | hvu
    · rw [min_eq_left huv] at h0 hwuv
      exact hu ⟨h0, hwuv.1.trans hw.2⟩
    · rw [min_eq_right hvu] at h0 hwuv
      exact hv ⟨h0, hwuv.1.trans hw.2⟩
  have hmax : 1 ≤ max u v := by
    by_contra h
    have h1 : max u v < 1 := lt_of_not_ge h
    rcases le_total u v with huv | hvu
    · rw [max_eq_right huv] at h1 hwuv
      exact hv ⟨hw.1.trans hwuv.2, h1⟩
    · rw [max_eq_left hvu] at h1 hwuv
      exact hu ⟨hw.1.trans hwuv.2, h1⟩
  exact fun _ hz ↦ ⟨hmin.trans hz.1, hz.2.trans hmax⟩

theorem segment_subset_of_lineMap_of_ends_outside {b c p q x : Plane}
    (hbc : b ≠ c) (hp : ∃ u : ℝ, p = AffineMap.lineMap b c u)
    (hq : ∃ v : ℝ, q = AffineMap.lineMap b c v)
    (hx : x ∈ openSegment ℝ b c) (hxseg : x ∈ openSegment ℝ p q)
    (hpout : p ∉ openSegment ℝ b c) (hqout : q ∉ openSegment ℝ b c) :
    segment ℝ b c ⊆ segment ℝ p q := by
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨v, rfl⟩ := hq
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hf := AffineMap.lineMap_injective (k := ℝ) hbc
  rw [← image_openSegment] at hxseg
  obtain ⟨w', hw', he⟩ := hxseg
  have hew : w' = w := hf he
  subst w'
  have hu : u ∉ Ioo (0 : ℝ) 1 := fun hu ↦ hpout (lineMap_mem_openSegment ℝ b c hu)
  have hv : v ∉ Ioo (0 : ℝ) 1 := fun hv ↦ hqout (lineMap_mem_openSegment ℝ b c hv)
  rw [segment_eq_image_lineMap, ← image_segment]
  exact image_mono (unit_segment_subset_of_meets_of_ends_outside hw hw' hu hv)

end Reeken.Geometry
