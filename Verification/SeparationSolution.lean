import Schoenflies.PrePolygonSep

open Set

namespace Verification

/-- Finite polygonal separation, independently stated with explicit cyclic segments.
Collinear consecutive edges are allowed, but distinct edges can only meet at endpoints. -/
theorem finite_polygon_separation (m : ℕ)
    (v : ZMod (m + 3) → EuclideanSpace ℝ (Fin 2))
    (hi : Function.Injective v)
    (he : ∀ i j, i ≠ j →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) ⊆ {v i, v (i + 1)}) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
      U ∪ V = (⋃ i, segment ℝ (v i) (v (i + 1)))ᶜ ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = ⋃ i, segment ℝ (v i) (v (i + 1)) ∧
      frontier V = ⋃ i, segment ℝ (v i) (v (i + 1)) := by
  let p : Schoenflies.PrePolygon m := ⟨v, hi, he⟩
  have h := p.isSeparating_carrier
  exact ⟨Schoenflies.inside p.carrier, Schoenflies.outside p.carrier,
    h.isOpen_inside, h.isOpen_outside,
    h.isOpen_inside.isConnected_iff_isPathConnected.mp h.isConnected_inside,
    h.isOpen_outside.isConnected_iff_isPathConnected.mp h.isConnected_outside,
    Schoenflies.disjoint_inside_outside, Schoenflies.inside_union_outside _,
    h.isBounded_inside, h.not_isBounded_outside, h.frontier_inside, h.frontier_outside⟩

end Verification
