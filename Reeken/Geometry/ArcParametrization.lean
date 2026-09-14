import Reeken.Geometry.ArcIntersection
import Reeken.Geometry.PolygonSeparation
import Schoenflies.PrePolygonArc

/-! # Injective parametrizations of the actual polygon cut arcs -/

open Set Schoenflies

namespace Reeken.Geometry.InscribedPolygon

variable {f : SimpleLoop Plane} (p : InscribedPolygon f)

theorem cyclicIndex_natCast (hn : 2 ≤ p.n) (j : Fin (p.n + 1)) :
    p.cyclicIndex hn (j.val : ZMod (p.n - 2 + 3)) = j := by
  apply Fin.ext
  change (j.val : ZMod (p.n - 2 + 3)).val = j.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := j.isLt; omega)]

theorem toPrePolygon_edge (hn : 2 ≤ p.n) (hp : p.Simple) (j : ZMod (p.n - 2 + 3)) :
    (p.toPrePolygon hn hp).edge j = p.edge (p.cyclicIndex hn j) := by
  change segment ℝ (p.vertex (p.cyclicIndex hn j))
    (p.vertex (p.cyclicIndex hn (j + 1))) = _
  rw [p.cyclicIndex_add_one]
  rfl

theorem toPrePolygon_forwardArc (hn : 2 ≤ p.n) (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a < b) :
    (p.toPrePolygon hn hp).arc (a.val : ZMod (p.n - 2 + 3)) (b.val - a.val) =
      p.forwardArc a b := by
  have hind (t : ℕ) (ht : t < b.val - a.val) :
      p.cyclicIndex hn ((a.val : ZMod (p.n - 2 + 3)) + t) =
        ⟨a.val + t, by have := b.isLt; omega⟩ := by
    apply Fin.ext
    change (((a.val : ZMod (p.n - 2 + 3)) + t)).val = a.val + t
    rw [← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  ext x
  rw [PrePolygon.mem_arc_iff]
  constructor
  · rintro ⟨t, ht, hx⟩
    rw [p.toPrePolygon_edge, hind t ht] at hx
    exact Or.inr ⟨_, by change a.val ≤ a.val + t; omega,
      by change a.val + t < b.val; omega, hx⟩
  · rintro (rfl | ⟨j, haj, hjb, hx⟩)
    · refine ⟨0, by omega, ?_⟩
      rw [Nat.cast_zero, add_zero, p.toPrePolygon_edge, p.cyclicIndex_natCast]
      exact left_mem_segment ℝ _ _
    · refine ⟨j.val - a.val, by omega, ?_⟩
      rw [p.toPrePolygon_edge, hind _ (by omega)]
      have hj : (⟨a.val + (j.val - a.val), by have := b.isLt; omega⟩ : Fin (p.n + 1)) = j := by
        apply Fin.ext
        change a.val + (j.val - a.val) = j.val
        omega
      rwa [hj]

/-- The finite split gives precisely the two arcs used in the nonstandard argument. -/
theorem Simple.isArcBetween_cut_arcs (hp : p.Simple) (hn : 2 ≤ p.n)
    {a b : Fin (p.n + 1)} (hab : a < b) :
    IsArcBetween (p.forwardArc a b) (p.vertex a) (p.vertex b) ∧
      IsArcBetween (p.backwardArc a b) (p.vertex a) (p.vertex b) := by
  let P := p.toPrePolygon hn hp
  let A : ZMod (p.n - 2 + 3) := a.val
  let k := b.val - a.val
  let N := p.n - 2 + 3
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkN : k ≤ p.n - 2 + 2 := by dsimp [k]; have := b.isLt; omega
  have hA : P.vertex A = p.vertex a := by
    change p.vertex (p.cyclicIndex hn (a.val : ZMod (p.n - 2 + 3))) = _
    rw [p.cyclicIndex_natCast]
  have hB : P.vertex (A + k) = p.vertex b := by
    have he : A + k = (b.val : ZMod (p.n - 2 + 3)) := by
      change (a.val : ZMod (p.n - 2 + 3)) + (b.val - a.val : ℕ) = _
      rw [← Nat.cast_add, Nat.add_sub_of_le (show a.val ≤ b.val from hab.le)]
    rw [he]
    change p.vertex (p.cyclicIndex hn (b.val : ZMod (p.n - 2 + 3))) = _
    rw [p.cyclicIndex_natCast]
  have hF : P.arc A k = p.forwardArc a b := p.toPrePolygon_forwardArc hn hp hab
  have hreturn : A + k + (N - k : ℕ) = A := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le (by dsimp [N]; omega)]
    change A + ((p.n - 2 + 3 : ℕ) : ZMod (p.n - 2 + 3)) = A
    rw [ZMod.natCast_self, add_zero]
  have hU : p.forwardArc a b ∪ P.arc (A + k) (N - k) = p.trace := by
    rw [← hF, P.arc_union A (by omega), p.toPrePolygon_carrier]
  have hI : p.forwardArc a b ∩ P.arc (A + k) (N - k) = {p.vertex a, p.vertex b} := by
    rw [← hF, P.arc_inter A hk hkN, hA, hB]
  have hBack : P.arc (A + k) (N - k) = p.backwardArc a b := by
    ext x
    have hu := congrArg (fun s : Set Plane ↦ x ∈ s) (hU.trans (p.arcs_union a b).symm)
    have hi := congrArg (fun s : Set Plane ↦ x ∈ s) (hI.trans (hp.arcs_inter hab.le).symm)
    simp only [mem_union, mem_inter_iff] at hu hi
    by_cases hx : x ∈ p.forwardArc a b
    · simpa only [hx, true_and] using Iff.of_eq hi
    · simpa only [hx, false_or] using Iff.of_eq hu
  constructor
  · have h := P.isArcBetween_arc A hk hkN
    rwa [hF, hA, hB] at h
  · have h := (P.isArcBetween_arc (A + k) (k := N - k)
      (by dsimp [N]; omega) (by dsimp [N]; omega)).reverse
    rwa [hBack, hreturn, hA, hB] at h

end Reeken.Geometry.InscribedPolygon
