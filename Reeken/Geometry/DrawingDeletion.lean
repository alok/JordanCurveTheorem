import Schoenflies.Graph.Trace

/-! # Vertex deletion detected by the punctured geometric drawing

If the geometric carrier remains connected after a vertex is removed, the finite
graph does too. Incident edges are assigned to the component of their other end;
the resulting closed geometric sets can meet only at the removed vertex.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

private def vertexSupport (G : Graph Plane β) (drawing : β → ℝ → Plane)
    (A : Set Plane) : Set Plane :=
  A ∪ ⋃ e ∈ E(G), ⋃ (_ : ∃ u ∈ A, G.Inc e u), Graph.edgeArc drawing e

private theorem isClosed_vertexSupport [G.Finite] (hd : G.IsDrawing drawing)
    {A : Set Plane} (hA : A ⊆ V(G)) : IsClosed (vertexSupport G drawing A) := by
  apply IsCompact.isClosed
  apply ((Graph.finite_vertexSet (G := G)).subset hA).isCompact.union
  apply (Graph.finite_edgeSet (G := G)).isCompact_biUnion
  intro e he
  exact isCompact_iUnion fun _ ↦ hd.isCompact_edgeArc he

private theorem mem_vertexSupport_of_edge {A : Set Plane} {e : β} {u x : Plane}
    (hu : u ∈ A) (heu : G.Inc e u) (hx : x ∈ Graph.edgeArc drawing e) :
    x ∈ vertexSupport G drawing A := by
  obtain ⟨v, huv⟩ := heu
  exact Or.inr (mem_iUnion₂.mpr ⟨e, huv.edge_mem,
    mem_iUnion.mpr ⟨⟨u, hu, v, huv⟩, hx⟩⟩)

private theorem vertexSupport_vertex (hd : G.IsDrawing drawing) {A : Set Plane} {c z : Plane}
    (hstable : ∀ {e u v}, G.IsLink e u v → u ∈ A → v ≠ c → v ∈ A)
    (hzV : z ∈ V(G)) (hzc : z ≠ c) (hz : z ∈ vertexSupport G drawing A) : z ∈ A := by
  rcases hz with hz | hz
  · exact hz
  obtain ⟨e, _, hz⟩ := mem_iUnion₂.mp hz
  obtain ⟨⟨u, hu, v, huv⟩, hze⟩ := mem_iUnion.mp hz
  rcases hd.vertex_mem_edgeArc huv hzV hze with rfl | rfl
  · exact hu
  · exact hstable huv hu hzc

private theorem vertexSupport_inter_subset (hd : G.IsDrawing drawing)
    {A B : Set Plane} {c : Plane} (hA : A ⊆ V(G) \ {c}) (hB : B ⊆ V(G) \ {c})
    (hdis : Disjoint A B)
    (hstableA : ∀ {e u v}, G.IsLink e u v → u ∈ A → v ≠ c → v ∈ A)
    (hstableB : ∀ {e u v}, G.IsLink e u v → u ∈ B → v ≠ c → v ∈ B) :
    vertexSupport G drawing A ∩ vertexSupport G drawing B ⊆ {c} := by
  rintro z ⟨hzA, hzB⟩
  by_contra hzc
  have hzc : z ≠ c := hzc
  by_cases hzV : z ∈ V(G)
  · exact Set.disjoint_left.mp hdis
      (vertexSupport_vertex hd hstableA hzV hzc hzA)
      (vertexSupport_vertex hd hstableB hzV hzc hzB)
  have hze : ∃ e ∈ E(G), (∃ u ∈ A, G.Inc e u) ∧ z ∈ Graph.edgeArc drawing e := by
    rcases hzA with hzA | hzA
    · exact (hzV (hA hzA).1).elim
    obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp hzA
    obtain ⟨ha, hza⟩ := mem_iUnion.mp hz
    exact ⟨e, he, ha, hza⟩
  have hzf : ∃ e ∈ E(G), (∃ u ∈ B, G.Inc e u) ∧ z ∈ Graph.edgeArc drawing e := by
    rcases hzB with hzB | hzB
    · exact (hzV (hB hzB).1).elim
    obtain ⟨e, he, hz⟩ := mem_iUnion₂.mp hzB
    obtain ⟨hb, hzb⟩ := mem_iUnion.mp hz
    exact ⟨e, he, hb, hzb⟩
  obtain ⟨e, he, ⟨u, hu, heu⟩, hze⟩ := hze
  obtain ⟨g, hg, ⟨v, hv, hgv⟩, hzg⟩ := hzf
  have heg : e = g := hd.unique_edge_at he hg hzV hze hzg
  subst g
  obtain ⟨w, hvw⟩ := hgv
  have hvS : v ∈ vertexSupport G drawing A :=
    mem_vertexSupport_of_edge hu heu (hd.edge_isArcBetween hvw).left_mem
  exact Set.disjoint_left.mp hdis
    (vertexSupport_vertex hd hstableA (hB hv).1 (hB hv).2 hvS) hv

private theorem punctured_subset_supports (hd : G.IsDrawing drawing) {A B : Set Plane}
    {c : Plane} (hcover : A ∪ B = V(G) \ {c}) :
    Graph.pointSet G drawing \ {c} ⊆ vertexSupport G drawing A ∪ vertexSupport G drawing B := by
  rintro x ⟨hx, hxc⟩
  have hmem : ∀ u ∈ V(G), u ≠ c → u ∈ A ∨ u ∈ B := by
    intro u hu huc
    rw [← mem_union, hcover]
    exact ⟨hu, huc⟩
  rcases hx with hx | hx
  · exact (hmem x hx hxc).imp Or.inl Or.inl
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
  have hsub : ∀ w ∈ V(G), w ≠ c → G.Inc e w →
      x ∈ vertexSupport G drawing A ∪ vertexSupport G drawing B := by
    intro w hw hwc hew
    rcases hmem w hw hwc with hwA | hwB
    · exact Or.inl (mem_vertexSupport_of_edge hwA hew hxe)
    · exact Or.inr (mem_vertexSupport_of_edge hwB hew hxe)
  by_cases huc : u = c
  · exact hsub v huv.right_mem (by intro hvc; exact hd.ne_of_isLink huv (huc.trans hvc.symm))
      huv.inc_right
  · exact hsub u huv.left_mem huc huv.inc_left

/-- Geometric connectedness after puncturing implies combinatorial connectedness after
deleting that vertex. No separation theorem for plane curves is used. -/
theorem connected_deleteVerts_of_punctured [G.Finite] (hd : G.IsDrawing drawing) (c : Plane)
    (hc : IsPreconnected (Graph.pointSet G drawing \ {c}))
    (hne : (V(G) \ {c}).Nonempty) : (G.deleteVerts {c}).Connected := by
  refine ⟨hne, fun a ha b hb ↦ ?_⟩
  by_contra hab
  let A := (G.deleteVerts {c}).component a
  let B := V(G.deleteVerts {c}) \ A
  have hA : A ⊆ V(G) \ {c} := Graph.component_subset_vertexSet
  have hB : B ⊆ V(G) \ {c} := sdiff_subset
  have hstableA : ∀ {e u v}, G.IsLink e u v → u ∈ A → v ≠ c → v ∈ A := by
    intro e u v huv hu hvc
    exact Graph.mem_component_of_isLink hu
      ((Graph.deleteVerts_isLink G {c}).mpr ⟨huv, (hA hu).2, hvc⟩)
  have hstableB : ∀ {e u v}, G.IsLink e u v → u ∈ B → v ≠ c → v ∈ B := by
    intro e u v huv hu hvc
    refine ⟨⟨huv.right_mem, hvc⟩, ?_⟩
    exact fun hv ↦ hu.2 (hstableA huv.symm hv hu.1.2)
  have hdis : Disjoint A B := disjoint_sdiff_right
  have hcover : A ∪ B = V(G) \ {c} := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hA hx
      · exact hB hx
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨hx, hxA⟩
  have hclosedA := isClosed_vertexSupport hd (hA.trans sdiff_subset)
  have hclosedB := isClosed_vertexSupport hd (hB.trans sdiff_subset)
  have hsep : (Graph.pointSet G drawing \ {c}) ∩
      (vertexSupport G drawing A ∩ vertexSupport G drawing B) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxs⟩
    exact hx.2 (vertexSupport_inter_subset hd hA hB hdis hstableA hstableB hxs)
  have ha' : a ∈ A := Graph.mem_component_self ha
  have hb' : b ∈ B := ⟨hb, hab⟩
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hc _ _ hclosedA hclosedB
      (punctured_subset_supports hd hcover) hsep with hsub | hsub
  · exact hab (vertexSupport_vertex hd hstableA hb.1 hb.2 (hsub ⟨Or.inl hb.1, hb.2⟩))
  · exact Set.disjoint_left.mp hdis ha'
      (vertexSupport_vertex hd hstableB ha.1 ha.2 (hsub ⟨Or.inl ha.1, ha.2⟩))

end Reeken.Geometry
