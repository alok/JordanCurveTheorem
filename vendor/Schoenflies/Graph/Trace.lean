/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.FaceCyclesLand

/-! # Tracing a finite plane drawing on a subset

Generic finite-graph excerpts from `CommonSubdivision.lean` at the pinned upstream
revision. No cell-structure or finite-transfer assembly is imported.
-/

open Set
open scoped Graph

namespace Graph

open Schoenflies

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
  {e : β} {x y : Plane}

/-- A finite plane graph with nonempty, preconnected point set is combinatorially connected. -/
theorem connected_of_isPreconnected_pointSet [G.Finite]
    (hdraw : IsDrawing G drawing) (hconn : IsPreconnected (pointSet G drawing))
    (hne : V(G).Nonempty) : G.Connected := by
  refine ⟨hne, fun x hx y hy => ?_⟩
  by_contra hxy
  let A : Graph Plane β := G.induce (G.component x)
  let B : Graph Plane β := G.induce (V(G) \ G.component x)
  have hAle : A ≤ G := G.induce_le component_subset_vertexSet
  have hBle : B ≤ G := G.induce_le Set.sdiff_subset
  have : A.Finite := Graph.Finite.of_le hAle
  have : B.Finite := Graph.Finite.of_le hBle
  have hAclosed : IsClosed (pointSet A drawing) := (hdraw.mono hAle).isClosed_pointSet
  have hBclosed : IsClosed (pointSet B drawing) := (hdraw.mono hBle).isClosed_pointSet
  have hcover : pointSet G drawing ⊆ pointSet A drawing ∪ pointSet B drawing := by
    intro z hz
    rcases hz with hzV | hzE
    · by_cases hzC : z ∈ G.component x
      · exact Or.inl (Or.inl hzC)
      · exact Or.inr (Or.inl ⟨hzV, hzC⟩)
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
      obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
      by_cases huC : u ∈ G.component x
      · have hvC : v ∈ G.component x := mem_component_of_isLink huC huv
        exact Or.inl (Or.inr (Set.mem_iUnion₂_of_mem
          (show e ∈ E(A) by
            rw [edgeSet_eq_setOfPred_exists_isLink]
            exact ⟨u, v, huv, huC, hvC⟩) hze))
      · have hvC : v ∉ G.component x := by
          intro hvC
          exact huC (mem_component_of_isLink hvC huv.symm)
        exact Or.inr (Or.inr (Set.mem_iUnion₂_of_mem
          (show e ∈ E(B) by
            rw [edgeSet_eq_setOfPred_exists_isLink]
            exact ⟨u, v, huv, ⟨huv.left_mem, huC⟩, ⟨huv.right_mem, hvC⟩⟩) hze))
  have hAB : Disjoint (pointSet A drawing) (pointSet B drawing) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    rcases hzA with hzAV | hzAE <;> rcases hzB with hzBV | hzBE
    · exact hzBV.2 hzAV
    · obtain ⟨e, heB, hze⟩ := Set.mem_iUnion₂.1 hzBE
      rw [edgeSet_eq_setOfPred_exists_isLink] at heB
      obtain ⟨u, v, huv, huB, hvB⟩ := heB
      have hzinc := hdraw.vertex_mem_edgeArc huv (component_subset_vertexSet hzAV) hze
      rcases hzinc with rfl | rfl
      exacts [huB.2 hzAV, hvB.2 hzAV]
    · obtain ⟨e, heA, hze⟩ := Set.mem_iUnion₂.1 hzAE
      rw [edgeSet_eq_setOfPred_exists_isLink] at heA
      obtain ⟨u, v, huv, huA, hvA⟩ := heA
      have hzinc := hdraw.vertex_mem_edgeArc huv hzBV.1 hze
      rcases hzinc with rfl | rfl
      exacts [hzBV.2 huA, hzBV.2 hvA]
    · obtain ⟨e, heA, hzeA⟩ := Set.mem_iUnion₂.1 hzAE
      obtain ⟨f, hfB, hzfB⟩ := Set.mem_iUnion₂.1 hzBE
      have heG : e ∈ E(G) := hAle.edgeSet_mono heA
      have hfG : f ∈ E(G) := hBle.edgeSet_mono hfB
      have hef : e ≠ f := by
        intro hef
        subst f
        rw [edgeSet_eq_setOfPred_exists_isLink] at heA hfB
        obtain ⟨u, v, huv, huA, -⟩ := heA
        obtain ⟨u', v', huv', huB, hvB⟩ := hfB
        rcases huv.left_eq_or_eq huv' with h | h
        · exact huB.2 (h ▸ huA)
        · exact hvB.2 (h ▸ huA)
      obtain ⟨hzV, ⟨u, heu⟩, ⟨v, hfv⟩⟩ :=
        hdraw.edge_inter heG hfG hef hzeA hzfB
      rw [edgeSet_eq_setOfPred_exists_isLink] at heA hfB
      obtain ⟨a, b, hab, haA, hbA⟩ := heA
      obtain ⟨c, d, hcd, hcB, hdB⟩ := hfB
      rcases heu.left_eq_or_eq hab with rfl | rfl <;>
        rcases hfv.left_eq_or_eq hcd with rfl | rfl
      all_goals first | exact hcB.2 haA | exact hdB.2 haA | exact hcB.2 hbA | exact hdB.2 hbA
  have hdisj : pointSet G drawing ∩ (pointSet A drawing ∩ pointSet B drawing) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzA, hzB⟩
    exact Set.disjoint_left.1 hAB hzA hzB
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hconn
      _ _ hAclosed hBclosed hcover hdisj) with hsub | hsub
  · have hyB : y ∈ pointSet B drawing := Or.inl ⟨hy, hxy⟩
    exact Set.disjoint_left.1 hAB (hsub (Or.inl hy)) hyB
  · have hxA : x ∈ pointSet A drawing := Or.inl (mem_component_self hx)
    exact Set.disjoint_left.1 hAB hxA (hsub (Or.inl hx))

/-- The part of a drawn graph supported on a prescribed set. -/
def traceGraph (G : Graph Plane β) (drawing : β → ℝ → Plane) (A : Set Plane) :
    Graph Plane β :=
  (G.restrict {e | edgeArc drawing e ⊆ A}).induce (V(G) ∩ A)

/-- The vertices retained by a trace graph. -/
@[simp] theorem traceGraph_vertexSet (A : Set Plane) :
    V(traceGraph G drawing A) = V(G) ∩ A := rfl

/-- A trace edge is exactly an ambient edge whose full arc and endpoints lie in the support. -/
@[simp] theorem traceGraph_isLink (A : Set Plane) :
    (traceGraph G drawing A).IsLink e x y ↔
      edgeArc drawing e ⊆ A ∧ G.IsLink e x y ∧ x ∈ A ∧ y ∈ A := by
  simp only [traceGraph, induce_isLink, restrict_isLink, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hsub, hlink⟩, ⟨-, hxA⟩, ⟨-, hyA⟩⟩
    exact ⟨hsub, hlink, hxA, hyA⟩
  · rintro ⟨hsub, hlink, hxA, hyA⟩
    exact ⟨⟨hsub, hlink⟩, ⟨hlink.left_mem, hxA⟩, ⟨hlink.right_mem, hyA⟩⟩

/-- A trace graph is a subgraph of its ambient graph. -/
theorem traceGraph_le (A : Set Plane) : traceGraph G drawing A ≤ G :=
  le_trans (induce_le Set.inter_subset_left) restrict_le

/-- Enlarging the support enlarges the trace graph. -/
theorem traceGraph_mono {A B : Set Plane} (hAB : A ⊆ B) :
    traceGraph G drawing A ≤ traceGraph G drawing B where
  vertexSet_mono := by
    rw [traceGraph_vertexSet, traceGraph_vertexSet]
    exact Set.inter_subset_inter_right _ hAB
  isLink_mono := by
    intro e x y hlink
    rw [traceGraph_isLink] at hlink ⊢
    exact ⟨hlink.1.trans hAB, hlink.2.1, hAB hlink.2.2.1, hAB hlink.2.2.2⟩

/-- The trace graph occupies only its prescribed support. -/
theorem pointSet_traceGraph_subset (A : Set Plane) :
    pointSet (traceGraph G drawing A) drawing ⊆ A := by
  rintro z (hz | hz)
  · exact hz.2
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
    rw [edgeSet_eq_setOfPred_exists_isLink] at he
    obtain ⟨x, y, hxy⟩ := he
    exact (traceGraph_isLink A).1 hxy |>.1 hze

/-- An absorbed subset of a finite drawing is exactly the point set of its trace graph. -/
theorem pointSet_traceGraph_eq (hdraw : IsDrawing G drawing) (A : Set Plane)
    (hsub : A ⊆ pointSet G drawing)
    (habsorb : ∀ ⦃e⦄, e ∈ E(G) →
      (edgeArc drawing e ∩ (A \ V(G))).Nonempty → edgeArc drawing e ⊆ A) :
    pointSet (traceGraph G drawing A) drawing = A := by
  apply Set.Subset.antisymm (pointSet_traceGraph_subset A)
  intro z hzA
  rcases hsub hzA with hzV | hzE
  · exact Or.inl ⟨hzV, hzA⟩
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
    by_cases hzVG : z ∈ V(G)
    · exact Or.inl ⟨hzVG, hzA⟩
    · have heA : edgeArc drawing e ⊆ A :=
        habsorb he ⟨z, ⟨hze, hzA, hzVG⟩⟩
      exact Or.inr (Set.mem_iUnion₂_of_mem
        (show e ∈ E(traceGraph G drawing A) by
          rw [edgeSet_eq_setOfPred_exists_isLink]
          obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
          have harc := hdraw.edge_isArcBetween hxy
          exact ⟨x, y, (traceGraph_isLink A).2
            ⟨heA, hxy, heA harc.left_mem, heA harc.right_mem⟩⟩)
        hze)

/-- A graph vertex lying on a drawn walk is one of the walk's combinatorial vertices. -/
theorem IsDrawing.mem_walkVertices_of_mem_edgesCover_walk (hdraw : IsDrawing G drawing)
    {u v z : Plane} {W : List β} (hW : G.IsWalk u W v)
    (hzV : z ∈ V(G)) (hz : z ∈ edgesCover drawing W) : z ∈ G.walkVertices u W := by
  obtain ⟨e, heW, hze⟩ := mem_edgesCover_iff.1 hz
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (hW.edge_mem heW)
  rcases hdraw.vertex_mem_edgeArc hxy hzV hze with rfl | rfl
  · exact mem_walkVertices_of_mem_covered ⟨e, heW, hxy.inc_left⟩
  · exact mem_walkVertices_of_mem_covered ⟨e, heW, hxy.inc_right⟩

/-- Adding edges without adding vertices preserves 2-connectivity. -/
theorem IsTwoConnected.spanning_mono {α δ : Type*} {A B : Graph α δ}
    (hA : A.IsTwoConnected) (hAB : A ≤ B) (hV : V(B) ⊆ V(A)) :
    B.IsTwoConnected where
  hasThreeVertices := hA.hasThreeVertices.mono hAB.vertexSet_mono
  connected := by
    obtain ⟨u, hu⟩ := hA.connected.nonempty
    exact Connected.of_hub (hAB.vertexSet_mono hu) fun x hx =>
      (hA.connected.reaches hu (hV hx)).mono hAB
  deleteVerts_connected := by
    intro x _
    have hdel := deleteVerts_mono hAB ({x} : Set α)
    obtain ⟨u, hu⟩ := (hA.deleteVerts_connected' x).nonempty
    exact Connected.of_hub (hdel.vertexSet_mono hu) fun y hy =>
      ((hA.deleteVerts_connected' x).reaches hu (by
        rw [vertexSet_deleteVerts] at hy ⊢
        exact ⟨hV hy.1, hy.2⟩)).mono hdel

end Graph
