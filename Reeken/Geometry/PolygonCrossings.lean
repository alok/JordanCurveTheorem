import Reeken.Geometry.MinimalPolygon
import Reeken.Geometry.PointArcs

/-! # A minimal admissible polygon has no nonadjacent crossings -/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SimpleLoop E}

theorem Minimal.nonadjacent_edges_disjoint {p : InscribedPolygon f} (hp : p.Minimal)
    (a b : Fin (p.n + 1)) (hab : a.val + 1 < b.val)
    (hproper : 0 < a.val ∨ b.val < p.n) : Disjoint (p.edge a) (p.edge b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain h | h := short_replacement_of_intersection hx hy
    (p.edgeLength_le_maxEdge a) (p.edgeLength_le_maxEdge b)
  · exact (not_le_of_gt (hp.no_short_chord a b hab hproper)) h
  · have ha : a ≠ Fin.last p.n := by
      intro ha
      have := b.isLt
      rw [ha] at hab
      simp only [Fin.val_last] at hab
      omega
    obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr ha
    rw [nextIndex_castSucc] at h
    by_cases hb : b = Fin.last p.n
    · subst b
      rw [nextIndex_last, dist_comm] at h
      apply (not_le_of_gt (hp.no_short_chord 0 k.succ ?_ ?_)) h
      · simp only [Fin.val_castSucc, Fin.val_last, lt_self_iff_false, or_false] at hproper
        simpa only [Fin.val_zero, Fin.val_succ, zero_add] using Nat.succ_lt_succ hproper
      · exact Or.inr (by simpa only [Fin.val_castSucc, Fin.val_last, Fin.val_succ] using hab)
    · obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hb
      rw [nextIndex_castSucc] at h
      apply (not_le_of_gt (hp.no_short_chord k.succ l.succ ?_ (Or.inl (by simp)))) h
      simpa only [Fin.val_castSucc, Fin.val_succ] using Nat.succ_lt_succ hab

end Reeken.Geometry.InscribedPolygon
