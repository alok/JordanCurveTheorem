import Reeken.Nonstandard.ChosenArcs
import Reeken.Geometry.NearestVertices
import Reeken.Geometry.BarrierBounds

/-! # Uniformly infinitesimal edge barriers against the outer polygon

Project each endpoint of a fine inner edge to a nearest outer vertex and close
the resulting three-segment path by the fixed small arc. Lemma 1(iii) makes the
whole family of barriers uniformly infinitesimal.
-/

open Filter Set Schoenflies Reeken.Geometry

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

noncomputable def vertexProjection (x : Plane) : Plane := p.vertex (p.nearestVertex x)

noncomputable def vertexArc (P : Piece) : List Piece := p.chosenArcPieces (p.nearestVertex P.1) (p.nearestVertex P.2)

noncomputable def vertexBarrier (P : Piece) : List Piece := edgeBarrier p.vertexProjection p.vertexArc P

theorem vertexArc_chain (hn : 2 ≤ p.n) (hp : p.Simple) (P : Piece) :
    IsChainFrom (p.vertexArc P) (p.vertexProjection P.1) (p.vertexProjection P.2) :=
  p.chosenArcPieces_chain hn hp _ _

theorem vertexArc_subset_trace (P : Piece) : cover (p.vertexArc P) ⊆ p.trace :=
  p.chosenArcPieces_subset_trace _ _

theorem vertexProjection_mem_trace (x : Plane) : p.vertexProjection x ∈ p.trace :=
  p.vertex_mem_trace _

end Reeken.Geometry.InscribedPolygon

namespace Reeken.NSA

variable {f : SimpleLoop Plane} (p : ℕ → InscribedPolygon f)
  (hmax : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, (p i).maxEdge < η)

include hmax

theorem nearestVertices_uniformly_near {s : ℕ → Set Plane}
    (hnear : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ s i,
      ∃ y ∈ (p i).trace, dist x y < η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ s i,
      dist x ((p i).vertexProjection x) < η := by
  intro η hη
  filter_upwards [hnear (η / 2) (by positivity), hmax (η / 2) (by positivity)] with i hi hmi
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hi x hx
  have h := (p i).nearestVertex_dist_le_of_near_trace (x := x) hy
  change dist x ((p i).vertexProjection x) ≤ _ at h
  linarith

theorem vertexBarriers_uniformly_small (hs : ∀ᶠ i in hyperfilter ℕ, (p i).Simple)
    (L : ℕ → List Piece)
    (hnear : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ x ∈ cover (L i),
      ∃ y ∈ (p i).trace, dist x y < η)
    (hedge : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ P ∈ L i, dist P.1 P.2 < η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ P ∈ L i,
      ∀ z ∈ cover ((p i).vertexBarrier P), dist z ((p i).vertexProjection P.1) < η := by
  have hproj := nearestVertices_uniformly_near p hmax hnear
  have hpairs : ∀ η : ℝ, 0 < η → ∀ᶠ i in hyperfilter ℕ, ∀ P ∈ L i,
      dist ((p i).vertexProjection P.1) ((p i).vertexProjection P.2) < η := by
    intro η hη
    filter_upwards [hproj (η / 3) (by positivity), hedge (η / 3) (by positivity)] with i hi hei
    intro P hP
    have hleft := hi P.1 (mem_cover hP (left_mem_segment ℝ _ _))
    have hright := hi P.2 (mem_cover hP (right_mem_segment ℝ _ _))
    have ht₁ := dist_triangle ((p i).vertexProjection P.1) P.1 ((p i).vertexProjection P.2)
    have ht₂ := dist_triangle P.1 P.2 ((p i).vertexProjection P.2)
    rw [dist_comm ((p i).vertexProjection P.1) P.1] at ht₁
    linarith [hei P hP]
  have harcs := chosenArcs_uniformly_small p hmax hs L
    (fun i P ↦ (p i).nearestVertex P.1) (fun i P ↦ (p i).nearestVertex P.2) hpairs
  intro η hη
  filter_upwards [hproj (η / 4) (by positivity), hedge (η / 4) (by positivity),
    harcs (η / 4) (by positivity)] with i hi hei hai
  intro P hP z hz
  have hbound := edgeBarrier_dist_le (show 0 ≤ η / 4 by positivity) (hei P hP).le
    (hi P.1 (mem_cover hP (left_mem_segment ℝ _ _))).le
    (hi P.2 (mem_cover hP (right_mem_segment ℝ _ _))).le
    (fun z hz ↦ (hai P hP z hz).le) z hz
  linarith

end Reeken.NSA
