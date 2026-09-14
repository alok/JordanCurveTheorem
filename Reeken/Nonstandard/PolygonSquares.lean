import Reeken.Geometry.SquareAnnulus
import Reeken.Nonstandard.ArcShadow

/-! # Choosing the generic local squares in the published common-boundary proof -/

open Filter Set Metric Topology
open Reeken.Geometry Schoenflies

namespace Reeken.NSA

variable {f : SimpleLoop Plane}

/-- An internal cut vertex has the standard image of its limiting parameter as standard part. -/
theorem cut_vertex_near (p : ℕ → InscribedPolygon f)
    (a : (i : ℕ) → Fin ((p i).n + 1)) {A : ℝ}
    (ha : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A)) :
    Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).vertex (a i))) (std (f A)) := by
  have ht : ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i)) ∈ starSet (Icc (0 : ℝ) 1) :=
    Eventually.of_forall fun i ↦ Ico_subset_Icc_self ((p i).time_mem (a i))
  have hA := closed_standard_part isClosed_Icc ht ha
  simpa only [map_ofSeq, map_std, InscribedPolygon.vertex] using
    ha.map_compact isCompact_Icc f.continuousOn ht ((std_mem_starSet _ _).mpr hA)

/-- The square radius can avoid every polygon vertex while keeping the two cut vertices
on opposite sides of the square boundary. The boundaries lie in a fixed compact annulus. -/
theorem exists_generic_polygon_squares (p : ℕ → InscribedPolygon f)
    (a b : (i : ℕ) → Fin ((p i).n + 1)) {A B r : ℝ}
    (ha : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (a i))) (std A))
    (hb : Near (ofSeq (U := hyperfilter ℕ) (fun i ↦ (p i).time (b i))) (std B))
    (hr : 0 < r) (hfar : 2 * r < Plane.supDist (f B) (f A)) :
    ∃ ρ : ℕ → ℝ, (∀ i, ρ i ∈ Ioo r (2 * r)) ∧
      (∀ i j, (p i).vertex j ∉ squareBoundary (f A) (ρ i)) ∧
      (∀ i, squareBoundary (f A) (ρ i) ⊆ squareAnnulus (f A) r (2 * r)) ∧
      ∀ᶠ i in hyperfilter ℕ, (p i).vertex (a i) ∈ Plane.openSquare (f A) (ρ i) ∧
        (p i).vertex (b i) ∉ Plane.closedSquare (f A) (ρ i) := by
  classical
  choose ρ hρ hav using fun i ↦ exists_generic_square_radius (p i).vertex (f A) hr
  have hva := (near_std_iff_tendsto _ _).mp (cut_vertex_near p a ha)
  have hvb := (near_std_iff_tendsto _ _).mp (cut_vertex_near p b hb)
  have hla := (continuous_supDist_left (f A)).continuousAt.tendsto.comp hva
  have hlb := (continuous_supDist_left (f A)).continuousAt.tendsto.comp hvb
  have hea : ∀ᶠ i in hyperfilter ℕ, Plane.supDist ((p i).vertex (a i)) (f A) < r :=
    hla (Iio_mem_nhds (by simpa using hr))
  have heb : ∀ᶠ i in hyperfilter ℕ, 2 * r < Plane.supDist ((p i).vertex (b i)) (f A) :=
    hlb (Ioi_mem_nhds hfar)
  refine ⟨ρ, hρ, hav, fun i ↦ squareBoundary_subset_annulus (hρ i).1.le (hρ i).2.le, ?_⟩
  filter_upwards [hea, heb] with i hai hbi
  exact ⟨hai.trans (hρ i).1, not_le_of_gt ((hρ i).2.trans hbi)⟩

end Reeken.NSA
