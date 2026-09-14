import Reeken.Geometry.ArcConnectivity
import Reeken.Geometry.SimplePolygon

/-! # A simple polygon's two arcs meet exactly at their cut vertices -/

open Set

namespace Reeken.Geometry.InscribedPolygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : SimpleLoop E} {p : InscribedPolygon f}

theorem Simple.vertex_mem_edge_iff (hp : p.Simple) (k i : Fin (p.n + 1)) :
    p.vertex k ∈ p.edge i ↔ k = i ∨ k = nextIndex p.n i := by
  constructor
  · intro hx
    by_cases hki : k = i
    · exact Or.inl hki
    rcases hp.2 k i hki (p.vertex k) ⟨left_mem_segment ℝ _ _, hx⟩ with h | h
    · exact Or.inl (hp.1 h.2)
    · exact Or.inr h.1.symm
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

theorem Simple.vertex_mem_forwardArc_iff (hp : p.Simple)
    {a b : Fin (p.n + 1)} (hab : a ≤ b) (k : Fin (p.n + 1)) :
    p.vertex k ∈ p.forwardArc a b ↔ a ≤ k ∧ k ≤ b := by
  constructor
  · rintro (he | ⟨i, hai, hib, hx⟩)
    · have hk := hp.1 he
      subst k
      exact ⟨le_rfl, hab⟩
    · rcases (hp.vertex_mem_edge_iff k i).mp hx with rfl | rfl
      · exact ⟨hai, hib.le⟩
      · have hi := nextIndex_val i
        have hb := b.isLt
        constructor <;> simp only [Fin.le_def] <;> split_ifs at hi <;> omega
  · rintro ⟨hak, hkb⟩
    exact (p.joinedIn_forwardArc hak hkb).target_mem

theorem Simple.vertex_mem_backwardArc_iff (hp : p.Simple)
    (a b k : Fin (p.n + 1)) :
    p.vertex k ∈ p.backwardArc a b ↔ k ≤ a ∨ b ≤ k := by
  constructor
  · rintro (he | ⟨i, hi, hx⟩)
    · have hk := hp.1 he
      subst k
      exact Or.inr le_rfl
    · rcases (hp.vertex_mem_edge_iff k i).mp hx with rfl | rfl
      · exact hi.imp (fun h ↦ h.le) id
      · have hnext := nextIndex_val i
        have ha := a.isLt
        simp only [Fin.le_def]
        split_ifs at hnext <;> rcases hi with hi | hi <;> omega
  · exact fun hk ↦ (p.joinedIn_backwardArc hk).target_mem

theorem Simple.arcs_inter (hp : p.Simple) {a b : Fin (p.n + 1)} (hab : a ≤ b) :
    p.forwardArc a b ∩ p.backwardArc a b = {p.vertex a, p.vertex b} := by
  ext x
  constructor
  · intro hx
    have hv : ∃ k, x = p.vertex k := by
      rcases hx.1 with h | ⟨i, hai, hib, hxi⟩
      · exact ⟨a, h⟩
      rcases hx.2 with h | ⟨j, hj, hxj⟩
      · exact ⟨b, h⟩
      have hij : i ≠ j := by
        intro h
        subst j
        rcases hj with hj | hj <;> omega
      rcases hp.2 i j hij x ⟨hxi, hxj⟩ with h | h
      · exact ⟨j, h.2⟩
      · exact ⟨i, h.2⟩
    obtain ⟨k, rfl⟩ := hv
    have hkF := (hp.vertex_mem_forwardArc_iff hab k).mp hx.1
    rcases (hp.vertex_mem_backwardArc_iff a b k).mp hx.2 with hka | hbk
    · exact Or.inl (congrArg p.vertex (le_antisymm hka hkF.1))
    · exact Or.inr (congrArg p.vertex (le_antisymm hkF.2 hbk))
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, (p.joinedIn_backwardArc (Or.inl le_rfl)).target_mem⟩
    · exact ⟨(p.joinedIn_forwardArc hab le_rfl).target_mem, Or.inl rfl⟩

end Reeken.Geometry.InscribedPolygon
