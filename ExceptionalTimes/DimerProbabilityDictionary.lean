import ExceptionalTimes.IndependentSupportExtension
import ExceptionalTimes.DimerExpansion
import ExceptionalTimes.DimerSelectedDictionary

/-! Exact finite probability dictionaries for the two semigroups used
in the expansion. Independent site refresh is at half the pair time. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.DimerProbabilityDictionary
noncomputable section

open DimerLaw DimerExpansion CenteredBlocks ManyDimerLaw ActivePartitionLaw
open EnvironmentVariance PairSquareSewing ProbeProduct CanonicalSpatialProduct
open IndependentAnnulusInput

variable {B : Type*} [Fintype B]

def pairedTest (slot : B×Fin 2 ↪ Site) (E : Configuration→Prop) (h : B→History) : ℝ :=
  indicator (E (pairDecode slot (fun b => (h b).1)) ∧ E (pairDecode slot (fun b => (h b).2)))

theorem canonical_probability (slot : B×Fin 2 ↪ Site) (E : Configuration→Prop)
    (t : ℝ) (ht : 0≤t) :
    kernel (fun _ : B => canonicalLaw t) (pairedTest slot E)=
      manyProbability (fun _ => refreshProbability t) (fun ω => E (pairDecode slot ω)) := by
  rw [manyProbability_eq_joint _ (fun _ => refreshProbability_nonneg ht)
    (fun _ => refreshProbability_le_one t)]
  exact (manyLaw_pi (fun _ : B => refreshProbability t)
    (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)
    (fun ω => indicator (E (pairDecode slot ω.1) ∧ E (pairDecode slot ω.2)))).symm

def siteHistories (B : Type*) : (B→History) ≃ (B×Fin 2→Bool×Bool) where
  toFun h bi := ((h bi.1).1 bi.2,(h bi.1).2 bi.2)
  invFun x b := (fun i => (x (b,i)).1,fun i => (x (b,i)).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem siteWeight (p : ℝ) (a b : Bool) :
    siteBase a b+p*siteInsertion a b=IndependentJointAssociation.pairWeight p (a,b) := by
  cases a <;> cases b <;>
    simp [siteBase,siteInsertion,IndependentJointAssociation.pairWeight] <;> ring

theorem refreshLaw_site_product (t : ℝ) (h : History) :
    refreshLaw t h=∏ i : Fin 2,IndependentJointAssociation.pairWeight
      (refreshProbability (t/2)) (h.1 i,h.2 i) := by
  simp only [refreshLaw,siteWeight,Fin.prod_univ_two]

theorem refresh_kernel_sites (t : ℝ) (ht : 0≤t)
    (f : (B×Fin 2→Bool×Bool)→ℝ) :
    kernel (fun _ : B => refreshLaw t) (fun h => f (siteHistories B h))=
      (IndependentJointAssociation.jointLaw (fun _ : B×Fin 2 => refreshProbability (t/2))
        (fun _ => refreshProbability_nonneg (by linarith))
        (fun _ => refreshProbability_le_one (t/2))).expect f := by
  unfold kernel FiniteLaw.expect
  rw [←(siteHistories B).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Equiv.apply_symm_apply]
  congr 1
  simp only [refreshLaw_site_product]
  change (∏ b : B,∏ i : Fin 2,IndependentJointAssociation.pairWeight
    (refreshProbability (t/2)) (ω (b,i)))=
      ∏ bi : B×Fin 2,IndependentJointAssociation.pairWeight (refreshProbability (t/2)) (ω bi)
  rw [Fintype.prod_prod_type]

theorem independent_site_embedding {A : Type*} [Fintype A] [DecidableEq A]
    (slot : A↪Site) (D : Finset Site) (hcover : ∀ v∈D,∃ a,slot a=v)
    (t : ℝ) (ht : 0≤t) (F : Configuration→Configuration→ℝ)
    (hlocal : ∀ a b a' b',Set.EqOn a a' D → Set.EqOn b b' D → F a b=F a' b') :
    (IndependentJointAssociation.jointLaw (fun _ : A => refreshProbability t)
      (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)).expect
      (fun ω => F (Function.extend slot (fun a => (ω a).1) (fun _ => false))
        (Function.extend slot (fun a => (ω a).2) (fun _ => false)))=
    (IndependentJointAssociation.jointLaw (fun _ : D => refreshProbability t)
      (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)).expect
      (fun ω => F (complete (fun v => (ω v).1)) (complete (fun v => (ω v).2))) := by
  let j : D↪A := ⟨fun v => Classical.choose (hcover v v.property),by
    intro v w h
    have hv := Classical.choose_spec (hcover v v.property)
    have hw := Classical.choose_spec (hcover w w.property)
    exact Subtype.ext (hv.symm.trans ((congrArg slot h).trans hw))⟩
  have hj (v : D) : slot (j v)=v := Classical.choose_spec (hcover v v.property)
  have hagree (ω : A→Bool) : Set.EqOn (Function.extend slot ω (fun _ => false))
      (complete (fun v => ω (j v))) D := by
    intro v hv
    change v∈D at hv
    have he : slot (j ⟨v,hv⟩)=v := hj ⟨v,hv⟩
    rw [←he,slot.injective.extend_apply]
    rw [he]
    simp [complete,hv]
  have he (ω : A→Bool×Bool) :
      F (Function.extend slot (fun a => (ω a).1) (fun _ => false))
        (Function.extend slot (fun a => (ω a).2) (fun _ => false))=
      F (complete (fun v => (ω (j v)).1)) (complete (fun v => (ω (j v)).2)) :=
    hlocal _ _ _ _ (hagree _) (hagree _)
  rw [FiniteLaw.expect_congr _ he]
  exact IndependentSupportExtension.pi_restrict j
    (fun _ => IndependentJointAssociation.pairLaw (refreshProbability t)
      (refreshProbability_nonneg ht) (refreshProbability_le_one t))
    (fun ω => F (complete (fun v => (ω v).1)) (complete (fun v => (ω v).2)))

theorem refresh_probability (slot : B×Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀ v∈D,∃ b,slot b=v) (E : Configuration→Prop)
    (hlocal : ∀ ω η,Set.EqOn ω η D → (E ω ↔ E η)) (t : ℝ) (ht : 0≤t) :
    kernel (fun _ : B => refreshLaw t) (pairedTest slot E)=jointProbability D (t/2) E := by
  let F : (B×Fin 2→Bool×Bool)→ℝ := fun ω =>
    indicator (E (Function.extend slot (fun a => (ω a).1) (fun _ => false)) ∧
      E (Function.extend slot (fun a => (ω a).2) (fun _ => false)))
  change kernel (fun _ : B => refreshLaw t) (fun h => F (siteHistories B h))=_
  rw [refresh_kernel_sites t ht,jointProbability_eq_law D (t/2) (by linarith)]
  exact independent_site_embedding slot D hcover (t/2) (by linarith)
    (fun a b => indicator (E a ∧ E b))
    (fun a b a' b' ha hb => congrArg indicator (propext (and_congr (hlocal _ _ ha) (hlocal _ _ hb))))

#print axioms canonical_probability
#print axioms refresh_probability
end
end ExceptionalTimes.DimerProbabilityDictionary
