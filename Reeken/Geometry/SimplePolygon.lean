import Reeken.Geometry.PolygonCrossings
import Reeken.Geometry.CyclicIndices
import Reeken.Geometry.Backtracking

/-! # Simplicity of minimal polygons, including adjacent overlaps -/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] {f : SimpleLoop E}

theorem vertex_injective (p : InscribedPolygon f) : Function.Injective p.vertex := by
  intro a b hab
  exact p.increasing.injective (f.injectiveOn (p.time_mem a) (p.time_mem b) hab)

theorem Minimal.no_short_chord_cyclic {p : InscribedPolygon f} (hp : p.Minimal)
    {a b : Fin (p.n + 1)} (hab : Nonadjacent a b) :
    p.maxEdge < dist (p.vertex a) (p.vertex b) := by
  rcases lt_or_gt_of_ne hab.1 with h | h
  · obtain ⟨hgap, hproper⟩ := hab.ordered h
    exact hp.no_short_chord a b hgap hproper
  · obtain ⟨hgap, hproper⟩ := hab.symm.ordered h
    simpa only [dist_comm] using hp.no_short_chord b a hgap hproper

variable [NormedSpace ℝ E]

theorem Minimal.disjoint_edges {p : InscribedPolygon f} (hp : p.Minimal)
    {a b : Fin (p.n + 1)} (hab : Nonadjacent a b) : Disjoint (p.edge a) (p.edge b) := by
  rcases lt_or_gt_of_ne hab.1 with h | h
  · obtain ⟨hgap, hproper⟩ := hab.ordered h
    exact hp.nonadjacent_edges_disjoint a b hgap hproper
  · obtain ⟨hgap, hproper⟩ := hab.symm.ordered h
    exact (hp.nonadjacent_edges_disjoint b a hgap hproper).symm

theorem Minimal.adjacent_intersection {p : InscribedPolygon f} (hp : p.Minimal)
    (hn : 3 ≤ p.n) (i : Fin (p.n + 1)) {x : E}
    (hx : x ∈ p.edge i) (hy : x ∈ p.edge (nextIndex p.n i)) :
    x = p.vertex (nextIndex p.n i) := by
  by_contra h
  have hshort := dist_le_max_of_adjacent_overlap hx hy h
  have hbound := max_le (p.edgeLength_le_maxEdge i)
    (p.edgeLength_le_maxEdge (nextIndex p.n i))
  exact (not_le_of_gt (hp.no_short_chord_cyclic (nonadjacent_next_next hn i)))
    (hshort.trans hbound)

/-- Distinct vertices; different edges can meet only at their shared endpoint.
This includes the exclusion of backtracking along adjacent edges. -/
def Simple (p : InscribedPolygon f) : Prop :=
  Function.Injective p.vertex ∧
    ∀ i j, i ≠ j → ∀ x ∈ p.edge i ∩ p.edge j,
      (nextIndex p.n i = j ∧ x = p.vertex j) ∨
      (nextIndex p.n j = i ∧ x = p.vertex i)

theorem Minimal.simple {p : InscribedPolygon f} (hp : p.Minimal) (hn : 3 ≤ p.n) :
    p.Simple := by
  refine ⟨p.vertex_injective, fun i j hij x hx ↦ ?_⟩
  by_cases hnext : nextIndex p.n i = j
  · left
    refine ⟨hnext, ?_⟩
    subst j
    exact hp.adjacent_intersection hn i hx.1 hx.2
  by_cases hprev : nextIndex p.n j = i
  · right
    refine ⟨hprev, ?_⟩
    subst i
    exact hp.adjacent_intersection hn j hx.2 hx.1
  exact (Set.disjoint_left.mp (hp.disjoint_edges ⟨hij, hnext, hprev⟩) hx.1 hx.2).elim

end Reeken.Geometry.InscribedPolygon
