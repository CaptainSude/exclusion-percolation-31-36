import ExceptionalTimes.MatchingSupportExtension
import ExceptionalTimes.UnitMatchingTranslation

/-! Reversing the orientation of any selected dimers preserves their
literal canonical law. Every phase matching can be oriented positively. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ExceptionalTimes.DimerOrientation

noncomputable section

open DimerLaw ManyDimerLaw ActivePartitionLaw PairSquareSewing

variable {B : Type*}

def colorChange (e : PairGroup) : Color≃Color := Equiv.arrowCongr e (Equiv.refl Bool)

theorem count_colorChange (e : PairGroup) (ω : Color) :
    blackCount (colorChange e ω)=blackCount ω := by
  have he : e=1 ∨ e=swap := by
    have h := Finset.mem_univ e
    rw [pairGroup_univ] at h
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h
  rcases he with rfl | rfl
  · rfl
  · obtain ⟨a,b,rfl⟩ := color_cases ω
    cases a <;> cases b <;> decide

theorem weight_colorChange (e : PairGroup) (p : ℝ) (ω η : Color) :
    twoTimeWeight p (colorChange e ω) (colorChange e η)=twoTimeWeight p ω η := by
  simp only [twoTimeWeight_formula,(colorChange e).injective.eq_iff,count_colorChange]

def colorsChange (e : B→PairGroup) : (B→Color)≃(B→Color) where
  toFun ω b := colorChange (e b) (ω b)
  invFun ω b := (colorChange (e b)).symm (ω b)
  left_inv ω := by funext b; exact (colorChange (e b)).symm_apply_apply _
  right_inv ω := by funext b; exact (colorChange (e b)).apply_symm_apply _

theorem many_change [Fintype B] (e : B→PairGroup) (p : B→ℝ)
    (E : (B→Color)→Prop) :
    manyProbability p E=manyProbability p (fun ω => E (colorsChange e ω)) := by
  unfold manyProbability
  rw [← (colorsChange e).sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← (colorsChange e).sum_comp]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  unfold manyWeight
  exact Finset.prod_congr rfl (fun b _ => weight_colorChange (e b) (p b) (ω b) (η b))

def siteChange (e : B→PairGroup) : B×Fin 2 ≃ B×Fin 2 where
  toFun a := (a.1,e a.1 a.2)
  invFun a := (a.1,(e a.1).symm a.2)
  left_inv a := by simp
  right_inv a := by simp

def orientSlot (slot : B×Fin 2 ↪ Site) (e : B→PairGroup) : B×Fin 2 ↪ Site :=
  (siteChange e).toEmbedding.trans slot

@[simp] theorem orientSlot_apply (slot : B×Fin 2 ↪ Site) (e : B→PairGroup)
    (b : B) (i : Fin 2) : orientSlot slot e (b,i)=slot (b,e b i) := rfl

theorem decode_orient (slot : B×Fin 2 ↪ Site) (e : B→PairGroup) (ω : B→Color) :
    pairDecode (orientSlot slot e) ω=pairDecode slot (colorsChange e ω) := by
  funext v
  by_cases hv : ∃ a,slot a=v
  · obtain ⟨⟨b,i⟩,rfl⟩ := hv
    have he : orientSlot slot e (b,(e b).symm i)=slot (b,i) := by
      simp [orientSlot,siteChange]
    unfold pairDecode
    conv_lhs => rw [← he]
    rw [(orientSlot slot e).injective.extend_apply,slot.injective.extend_apply]
    rfl
  · have hn : ¬∃ a,orientSlot slot e a=v := by
      rintro ⟨a,ha⟩
      exact hv ⟨siteChange e a,ha⟩
    unfold pairDecode
    rw [Function.extend_apply' _ _ _ hn,Function.extend_apply' _ _ _ hv]

theorem probability_orient [Fintype B] (slot : B×Fin 2 ↪ Site) (e : B→PairGroup)
    (p : B→ℝ) (E : Configuration→Prop) :
    manyProbability p (fun ω => E (pairDecode slot ω))=
      manyProbability p (fun ω => E (pairDecode (orientSlot slot e) ω)) := by
  simp_rw [decode_orient]
  exact many_change e p (fun ω => E (pairDecode slot ω))

def positiveChange (phase : Bool) (slot : B×Fin 2 ↪ Site) (b : B) : PairGroup :=
  if ((slot (b,0)).1+(if phase then 1 else 0))%2=0 then 1 else swap

theorem positively_oriented (phase : Bool) (slot : B×Fin 2 ↪ Site)
    (hpair : ∀ b,slot (b,1)=UnitMatchingTranslation.partner phase (slot (b,0))) (b : B) :
    orientSlot slot (positiveChange phase slot) (b,1)=
      orientSlot slot (positiveChange phase slot) (b,0)+(1,0) := by
  have hp := hpair b
  by_cases he : ((slot (b,0)).1+(if phase then 1 else 0))%2=0
  · have hc : positiveChange phase slot b=1 := by simp only [positiveChange,ite_eq_left he]
    rw [orientSlot_apply,orientSlot_apply,hc]
    simpa only [Equiv.Perm.one_apply,UnitMatchingTranslation.partner,ite_eq_left he] using hp
  · have hp' : slot (b,1)=slot (b,0)-(1,0) := by
      simpa only [UnitMatchingTranslation.partner,ite_eq_right he] using hp
    have hc : positiveChange phase slot b=swap := by simp only [positiveChange,ite_eq_right he]
    rw [orientSlot_apply,orientSlot_apply,hc]
    change slot (b,0)=slot (b,1)+(1,0)
    rw [hp']
    exact (sub_add_cancel _ _).symm

theorem orient_covers (slot : B×Fin 2 ↪ Site) (e : B→PairGroup) (S : Set Site)
    (hcover : ∀ v∈S,∃ a,slot a=v) : ∀ v∈S,∃ a,orientSlot slot e a=v := by
  intro v hv
  obtain ⟨a,ha⟩ := hcover v hv
  refine ⟨(siteChange e).symm a,?_⟩
  simpa only [orientSlot,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply] using ha

theorem positive_zero_even (phase : Bool) (slot : B×Fin 2 ↪ Site)
    (hpair : ∀ b,slot (b,1)=UnitMatchingTranslation.partner phase (slot (b,0))) (b : B) :
    ((orientSlot slot (positiveChange phase slot) (b,0)).1+(if phase then 1 else 0))%2=0 := by
  by_cases he : ((slot (b,0)).1+(if phase then 1 else 0))%2=0
  · have hc : positiveChange phase slot b=1 := by simp only [positiveChange,ite_eq_left he]
    rw [orientSlot_apply,hc]
    exact he
  · have hp : slot (b,1)=slot (b,0)-(1,0) := by
      simpa only [UnitMatchingTranslation.partner,ite_eq_right he] using hpair b
    have hc : positiveChange phase slot b=swap := by simp only [positiveChange,ite_eq_right he]
    rw [orientSlot_apply,hc]
    change ((slot (b,1)).1+(if phase then 1 else 0))%2=0
    rw [hp]
    simp only [Prod.fst_sub]
    omega

theorem positive_phase (phase : Bool) (slot : B×Fin 2 ↪ Site)
    (hpair : ∀ b,slot (b,1)=UnitMatchingTranslation.partner phase (slot (b,0))) (b : B) :
    orientSlot slot (positiveChange phase slot) (b,1)=UnitMatchingTranslation.partner phase
      (orientSlot slot (positiveChange phase slot) (b,0)) := by
  rw [UnitMatchingTranslation.partner,ite_eq_left (positive_zero_even phase slot hpair b)]
  exact positively_oriented phase slot hpair b

#print axioms probability_orient
#print axioms positively_oriented
#print axioms positive_zero_even

end
end ExceptionalTimes.DimerOrientation
