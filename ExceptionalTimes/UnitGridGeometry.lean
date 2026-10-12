import ExceptionalTimes.UnitGridEdges

/-! Distinct literal integer unit edges meet only at endpoints. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing
namespace UnitGridEdge

theorem integer_cell_unique {a b : ℤ} {x : ℝ}
    (ha : (a:ℝ)<x ∧ x<(a:ℝ)+1) (hb : (b:ℝ)≤x ∧ x≤(b:ℝ)+1) : a=b := by
  have hab : (a:ℝ)<(b:ℝ)+1 := lt_of_lt_of_le ha.1 hb.2
  have hba : (b:ℝ)<(a:ℝ)+1 := lt_of_le_of_lt hb.1 ha.2
  have hab' : a<b+1 := by exact_mod_cast hab
  have hba' : b<a+1 := by exact_mod_cast hba
  omega

theorem eq_of_core_carrier {e f : UnitGridEdge} {p : ℝ × ℝ}
    (he : p ∈ e.core) (hf : p ∈ f.carrier) : e=f := by
  have hx : e.anchor.1=f.anchor.1 ∧ e.anchor.2=f.anchor.2 ∧ e.horizontal=f.horizontal := by
    cases hh : e.horizontal <;> cases hg : f.horizontal
    · simp only [core,carrier,hh,hg,Bool.false_eq_true,ite_false,mem_prod,
        mem_singleton_iff,mem_Ioo,mem_Icc] at he hf
      refine ⟨?_,integer_cell_unique he.2 hf.2,rfl⟩
      exact_mod_cast he.1.symm.trans hf.1
    · simp only [core,carrier,hh,hg,Bool.false_eq_true,ite_false,ite_true,mem_prod,
        mem_singleton_iff,mem_Ioo,mem_Icc] at he hf
      exact False.elim (not_integer_between e.anchor.2 he.2.1 he.2.2 ⟨f.anchor.2,hf.2.symm⟩)
    · simp only [core,carrier,hh,hg,Bool.false_eq_true,ite_false,ite_true,mem_prod,
        mem_singleton_iff,mem_Ioo,mem_Icc] at he hf
      exact False.elim (not_integer_between e.anchor.1 he.1.1 he.1.2 ⟨f.anchor.1,hf.1.symm⟩)
    · simp only [core,carrier,hh,hg,ite_true,mem_prod,
        mem_singleton_iff,mem_Ioo,mem_Icc] at he hf
      refine ⟨integer_cell_unique he.1 hf.1,?_,rfl⟩
      exact_mod_cast he.2.symm.trans hf.2
  cases e
  cases f
  simp only [mk.injEq]
  exact ⟨Prod.ext hx.1 hx.2.1,hx.2.2⟩

theorem core_of_not_endpoint {e : UnitGridEdge} {p : ℝ × ℝ}
    (hp : p ∈ e.carrier) (hfirst : p≠e.first) (hlast : p≠e.last) : p ∈ e.core := by
  cases hh : e.horizontal
  · simp only [carrier,core,hh,Bool.false_eq_true,ite_false,mem_prod,mem_singleton_iff,
      mem_Icc,mem_Ioo] at hp ⊢
    refine ⟨hp.1,lt_of_le_of_ne hp.2.1 ?_,lt_of_le_of_ne hp.2.2 ?_⟩
    · intro he
      exact hfirst (Prod.ext hp.1 he.symm)
    · intro he
      apply hlast
      simpa only [last,hh,Bool.false_eq_true,ite_false] using Prod.ext hp.1 he
  · simp only [carrier,core,hh,ite_true,mem_prod,mem_singleton_iff,
      mem_Icc,mem_Ioo] at hp ⊢
    refine ⟨⟨lt_of_le_of_ne hp.1.1 ?_,lt_of_le_of_ne hp.1.2 ?_⟩,hp.2⟩
    · intro he
      exact hfirst (Prod.ext he.symm hp.2)
    · intro he
      apply hlast
      simpa only [last,hh,ite_true] using Prod.ext he hp.2

theorem distinct_meet_at_endpoint {e f : UnitGridEdge} (hef : e≠f)
    {p : ℝ × ℝ} (he : p ∈ e.carrier) (hf : p ∈ f.carrier) :
    p=e.first ∨ p=e.last := by
  by_contra hn
  push Not at hn
  exact hef (eq_of_core_carrier (core_of_not_endpoint he hn.1 hn.2) hf)

theorem simple (s : Finset UnitGridEdge) :
    SimpleSegmentFamily (fun e : s => e.val.segment) := by
  intro e f hef p he hf
  have he' : p ∈ e.val.carrier := by rw [← e.val.segment_carrier]; exact he
  have hf' : p ∈ f.val.carrier := by rw [← f.val.segment_carrier]; exact hf
  exact distinct_meet_at_endpoint (fun h => hef (Subtype.ext h)) he' hf'

theorem carrier_closed (e : UnitGridEdge) : IsClosed e.carrier := by
  rw [← e.closure_core]
  exact isClosed_closure

theorem segment_level_integer (e : UnitGridEdge) : ∃ z : ℤ, e.segment.level=(z:ℝ) := by
  cases hh : e.horizontal
  · exact ⟨e.anchor.1,by simp [segment,AxialSegment.level,first,HexCells.center,hh]⟩
  · exact ⟨e.anchor.2,by simp [segment,AxialSegment.level,first,HexCells.center,hh]⟩

#print axioms simple

end UnitGridEdge
end ExceptionalTimes.PairSquareSewing

