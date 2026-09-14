import Reeken.Geometry.PathHomotopy
import Mathlib.Analysis.Convex.Contractible

/-! # Collapsing an attached convex piece

A closed convex piece can be removed when a continuous map collapses it into
its intersection with the remaining closed set and fixes that intersection.
The straight deformation is pasted with the identity on the remaining set.
This is the topological step for removing a triangle along an attached edge.
-/

open Set unitInterval
open scoped ContinuousMap

namespace Reeken.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A segment is a retract of the ambient normed space. The parameter is distance
from the first endpoint, divided by the length and truncated at one. -/
theorem exists_continuous_segment_retraction (a b : E) :
    ∃ r : E → E, Continuous r ∧ (∀ x, r x ∈ segment ℝ a b) ∧
      ∀ x ∈ segment ℝ a b, r x = x := by
  by_cases hab : a = b
  · subst b
    exact ⟨fun _ ↦ a, continuous_const, fun _ ↦ by simp, fun x hx ↦ by simpa [eq_comm] using hx⟩
  have hd : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
  let t : E → ℝ := fun x ↦ min (‖x - a‖ / ‖b - a‖) 1
  have ht0 : ∀ x, 0 ≤ t x := fun x ↦ le_min (div_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
  have ht1 : ∀ x, t x ≤ 1 := fun x ↦ min_le_right _ _
  refine ⟨fun x ↦ (1 - t x) • a + t x • b, by dsimp [t]; fun_prop, ?_, ?_⟩
  · intro x
    exact ⟨1 - t x, t x, sub_nonneg.mpr (ht1 x), ht0 x, sub_add_cancel _ _, rfl⟩
  · rintro x ⟨u, v, hu, hv, huv, rfl⟩
    have he : u • a + v • b - a = v • (b - a) := by
      have hu' : u = 1 - v := by linarith
      rw [hu']
      module
    have ht : t (u • a + v • b) = v := by
      dsimp [t]
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv, mul_div_cancel_right₀ _ hd]
      exact min_eq_left (by linarith)
    change (1 - t (u • a + v • b)) • a + t (u • a + v • b) • b = _
    rw [ht, show 1 - v = u by linarith]

theorem contractibleSpace_union_of_convex_attachment {A B : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (hconv : Convex ℝ A)
    (r : E → E) (hr : Continuous r) (hrA : MapsTo r A (A ∩ B))
    (hfix : ∀ x ∈ A ∩ B, r x = x) [ContractibleSpace B] :
    ContractibleSpace (A ∪ B : Set E) := by
  classical
  let ρ : E → E := A.piecewise r id
  have hρA : ∀ x ∈ A, ρ x = r x := fun x hx ↦ by simp [ρ, hx]
  have hρB : ∀ x ∈ B, ρ x = x := by
    intro x hx
    by_cases hxA : x ∈ A
    · simpa [ρ, hxA] using hfix x ⟨hxA, hx⟩
    · simp [ρ, hxA]
  have hρcont : ContinuousOn ρ (A ∪ B) :=
    ContinuousOn.union_of_isClosed
      (hr.continuousOn.congr fun x hx ↦ hρA x hx)
      (continuous_id.continuousOn.congr fun x hx ↦ hρB x hx) hA hB
  have hρmem : ∀ x ∈ A ∪ B, ρ x ∈ B := by
    intro x hx
    rcases hx with hx | hx
    · rw [hρA x hx]
      exact (hrA hx).2
    · rw [hρB x hx]
      exact hx
  let R : C((A ∪ B : Set E), B) :=
    ⟨fun x ↦ ⟨ρ x, hρmem x x.2⟩,
      (continuousOn_iff_continuous_domRestrict.mp hρcont).subtype_mk _⟩
  let inc : C(B, (A ∪ B : Set E)) :=
    ⟨fun x ↦ ⟨x, Or.inr x.2⟩, by fun_prop⟩
  have hsegment : ∀ x ∈ A ∪ B, segment ℝ (ρ x) x ⊆ A ∪ B := by
    intro x hx
    by_cases hxA : x ∈ A
    · rw [hρA x hxA]
      exact (hconv.segment_subset (hrA hxA).1 hxA).trans subset_union_left
    · rw [hρB x (hx.resolve_left hxA), segment_same]
      exact singleton_subset_iff.mpr hx
  have H : (inc.comp R).Homotopy (ContinuousMap.id (A ∪ B : Set E)) := {
    toFun := fun z ↦ ⟨(1 - (z.1 : ℝ)) • ρ z.2 + (z.1 : ℝ) • (z.2 : E),
      hsegment z.2 z.2.2 ⟨1 - (z.1 : ℝ), (z.1 : ℝ),
        sub_nonneg.mpr z.1.2.2, z.1.2.1, sub_add_cancel _ _, rfl⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hc : Continuous (fun x : (A ∪ B : Set E) ↦ ρ x) :=
        continuousOn_iff_continuous_domRestrict.mp hρcont
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (hc.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd))
    map_zero_left := by intro x; apply Subtype.ext; simp [R, inc]; rfl
    map_one_left := by intro x; apply Subtype.ext; simp
  }
  have hright : R.comp inc = ContinuousMap.id B := by
    ext x
    exact hρB x x.2
  let e : (A ∪ B : Set E) ≃ₕ B := {
    toFun := R
    invFun := inc
    left_inv := ⟨H⟩
    right_inv := hright ▸ ContinuousMap.Homotopic.refl _
  }
  exact e.contractibleSpace

/-- Removing a closed convex piece attached along one full segment preserves
contractibility. This includes a polygonal ear, without restrictions on its angles. -/
theorem contractibleSpace_union_of_segment_inter {A B : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (hconv : Convex ℝ A)
    (a b : E) (hinter : A ∩ B = segment ℝ a b) [ContractibleSpace B] :
    ContractibleSpace (A ∪ B : Set E) := by
  obtain ⟨r, hr, hmem, hfix⟩ := exists_continuous_segment_retraction a b
  exact contractibleSpace_union_of_convex_attachment hA hB hconv r hr
    (fun x _ ↦ hinter ▸ hmem x) (fun x hx ↦ hfix x (hinter ▸ hx))

end Reeken.Geometry
