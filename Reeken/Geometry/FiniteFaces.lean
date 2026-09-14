import Schoenflies.FaceCyclesLand
import Mathlib.Data.Set.Finite.Powerset

/-! # Finitely many faces of a finite polygonal 2-connected drawing

Each face is the inside or outside of the carrier of a subset of the finite edge set.
The powerset bound avoids choosing or counting parametrizations of boundary cycles.
-/

open Set Schoenflies
open scoped Graph

namespace Reeken.Geometry

theorem finite_faces {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    [G.Finite] (hd : G.IsDrawing drawing)
    (hpoly : ∀ e ∈ E(G), IsPolygonal (Graph.edgeArc drawing e)) (hG : G.IsTwoConnected) :
    {F | ∃ z ∈ Graph.exterior G drawing, Graph.face G drawing z = F}.Finite := by
  let carrier : Set β → Set Plane := fun S ↦ ⋃ e ∈ S, Graph.edgeArc drawing e
  have hf := (Graph.finite_edgeSet (G := G)).powerset
  apply ((hf.image (fun S ↦ inside (carrier S))).union
    (hf.image (fun S ↦ outside (carrier S)))).subset
  rintro F ⟨z, hz, rfl⟩
  obtain ⟨e, u, v, D, hc⟩ := Graph.face_cycles' hd hpoly hG z hz
  let S : Set β := {g | g ∈ e :: D}
  have hS : S ∈ 𝒫 E(G) := fun g hg ↦ hc.isCycle.isWalk_cons.edge_mem hg
  rcases hc.eq_inside_or_outside with h | h
  · exact Or.inl ⟨S, hS, h.symm⟩
  · exact Or.inr ⟨S, hS, h.symm⟩

end Reeken.Geometry
