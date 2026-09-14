import Reeken.Geometry.PolygonDeletion

/-! # Minimal admissible polygons and shortcut reduction

Finite minimization provides the termination step in loop cutting. The two explicit
deletions show that a minimal polygon has no short chord between nonadjacent vertices.
-/

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] {f : SimpleLoop E}

/-- The vertex count is minimal among admissible polygons with this edge bound. -/
def Minimal (p : InscribedPolygon f) : Prop :=
  ∀ q : InscribedPolygon f, q.maxEdge ≤ p.maxEdge → p.n ≤ q.n

theorem exists_minimal (p : InscribedPolygon f) :
    ∃ q : InscribedPolygon f, q.maxEdge ≤ p.maxEdge ∧ q.Minimal := by
  classical
  let P (n : ℕ) := ∃ q : InscribedPolygon f, q.n = n ∧ q.maxEdge ≤ p.maxEdge
  have hP : ∃ n, P n := ⟨p.n, p, rfl, le_rfl⟩
  obtain ⟨q, hqn, hq⟩ := Nat.find_spec hP
  refine ⟨q, hq, fun r hr ↦ ?_⟩
  rw [hqn]
  exact Nat.find_min' hP ⟨r, rfl, hr.trans hq⟩

/-- A short chord between cyclically nonadjacent vertices permits a strict reduction. -/
theorem exists_reduction_of_short_chord (p : InscribedPolygon f)
    (a b : Fin (p.n + 1)) (hab : a.val + 1 < b.val)
    (hproper : 0 < a.val ∨ b.val < p.n)
    (hshort : dist (p.vertex a) (p.vertex b) ≤ p.maxEdge) :
    ∃ q : InscribedPolygon f, q.n < p.n ∧ q.maxEdge ≤ p.maxEdge := by
  have hab' : a ≤ b := by omega
  by_cases hgap : p.time b - p.time a ≤ 1 / 2
  · let d := b.val - a.val - 1
    have hd : 0 < d := by omega
    have hb : a.val + d + 1 = b.val := by omega
    have hbound : a.val + d + 1 ≤ p.n := by have := b.isLt; omega
    have haeq : (⟨a.val, by omega⟩ : Fin (p.n + 1)) = a := rfl
    have hbeq : (⟨a.val + d + 1, by omega⟩ : Fin (p.n + 1)) = b := Fin.ext hb
    have hg : p.time ⟨a.val + d + 1, by omega⟩ - p.time ⟨a.val, by omega⟩ ≤ 1 / 2 := by
      simpa only [haeq, hbeq] using hgap
    refine ⟨p.deleteBetween a.val d hbound hg, ?_, ?_⟩
    · have hc := p.deleteBetween_count_lt a.val d hbound hg hd
      omega
    · apply p.deleteBetween_maxEdge_le
      simpa only [haeq, hbeq] using hshort
  · have hspan : 1 / 2 ≤ p.time b - p.time a := (lt_of_not_ge hgap).le
    refine ⟨p.slice a b hab' hspan, ?_, p.slice_maxEdge_le a b hab' hspan hshort⟩
    have hc := p.slice_count_lt a b hab' hspan hproper
    omega

theorem Minimal.no_short_chord {p : InscribedPolygon f} (hp : p.Minimal)
    (a b : Fin (p.n + 1)) (hab : a.val + 1 < b.val)
    (hproper : 0 < a.val ∨ b.val < p.n) :
    p.maxEdge < dist (p.vertex a) (p.vertex b) := by
  by_contra! h
  obtain ⟨q, hqn, hq⟩ := p.exists_reduction_of_short_chord a b hab hproper h
  exact (not_lt_of_ge (hp q hq)) hqn

end Reeken.Geometry.InscribedPolygon
