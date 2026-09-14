import Reeken.Nonstandard.PolygonArcs

/-! # Moving from points on edges to their incident vertices -/

open Filter Set
open Reeken.Geometry

namespace Reeken.NSA

variable {ι E : Type*} {U : Ultrafilter ι} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : SimpleLoop E} (p : ι → InscribedPolygon f)

theorem edge_point_near_vertex
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxEdge < ε)
    (j : (i : ι) → Fin ((p i).n + 1)) (x : ι → E)
    (hx : ∀ᶠ i in U, x i ∈ segment ℝ ((p i).vertex (j i))
      ((p i).vertex (nextIndex (p i).n (j i)))) :
    Near (ofSeq (U := U) x) (ofSeq (fun i ↦ (p i).vertex (j i))) := by
  intro ε hε
  filter_upwards [hx, hmax ε hε] with i hi hmi
  rw [dist_comm]
  exact (dist_left_le_of_mem_segment hi).trans_lt
    (((p i).edgeLength_le_maxEdge (j i)).trans_lt hmi)

theorem exists_incident_vertex (x : ι → E)
    (hx : ∀ᶠ i in U, x i ∈ (p i).trace) :
    ∃ j : (i : ι) → Fin ((p i).n + 1),
      ∀ᶠ i in U, x i ∈ segment ℝ ((p i).vertex (j i))
        ((p i).vertex (nextIndex (p i).n (j i))) := by
  classical
  let j (i : ι) : Fin ((p i).n + 1) :=
    if h : x i ∈ (p i).trace then Classical.choose (mem_iUnion.mp h) else 0
  refine ⟨j, hx.mono ?_⟩
  intro i hi
  simp only [j, dif_pos hi]
  exact Classical.choose_spec (mem_iUnion.mp hi)

theorem near_incident_vertices
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxEdge < ε)
    (a b : (i : ι) → Fin ((p i).n + 1)) (x y : ι → E)
    (hx : ∀ᶠ i in U, x i ∈ segment ℝ ((p i).vertex (a i))
      ((p i).vertex (nextIndex (p i).n (a i))))
    (hy : ∀ᶠ i in U, y i ∈ segment ℝ ((p i).vertex (b i))
      ((p i).vertex (nextIndex (p i).n (b i))))
    (hxy : Near (ofSeq (U := U) x) (ofSeq y)) :
    Near (ofSeq (U := U) (fun i ↦ (p i).vertex (a i)))
      (ofSeq (fun i ↦ (p i).vertex (b i))) :=
  (edge_point_near_vertex p hmax a x hx).symm.trans
    (hxy.trans (edge_point_near_vertex p hmax b y hy))

/-- An entire selected infinitesimal edge lies in its initial vertex's monad. -/
theorem edge_inMonad
    (hmax : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, (p i).maxEdge < ε)
    (j : (i : ι) → Fin ((p i).n + 1)) :
    InMonad (internalSet (U := U) (fun i ↦ segment ℝ ((p i).vertex (j i))
      ((p i).vertex (nextIndex (p i).n (j i)))))
      (ofSeq (fun i ↦ (p i).vertex (j i))) := by
  intro x hx
  obtain ⟨x, rfl⟩ := ofSeq_surjective x
  exact edge_point_near_vertex p hmax j x hx

end Reeken.NSA
