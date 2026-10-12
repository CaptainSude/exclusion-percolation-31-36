import ExceptionalTimes.CanonicalExtensionLaw
import ExceptionalTimes.IndependentAnnulusInput
import ExceptionalTimes.FairSiteRestriction

/-! Exact positive-time restriction of the independent two-replica law.
Unused site histories integrate to one; no limiting or dynamical input. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ExceptionalTimes.IndependentSupportExtension

noncomputable section

open EnvironmentVariance IndependentJointAssociation IndependentAnnulusInput
open PairSquareSewing DimerLaw

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  [DecidableEq A] [DecidableEq B]

local instance : DecidableEq (A⊕B) := fun a b => Classical.propDecidable (a=b)

theorem pi_relabel (e : A≃B) (μ : B→FiniteLaw X) (f : (B→X)→ℝ) :
    (FiniteLaw.pi μ).expect f =
      (FiniteLaw.pi (fun a => μ (e a))).expect
        (fun ω => f (fun b => ω (e.symm b))) := by
  unfold FiniteLaw.expect
  rw [← (Equiv.arrowCongr e (Equiv.refl X)).sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  change (∏ b,(μ b).weight (ω (e.symm b))) = ∏ a,(μ (e a)).weight (ω a)
  rw [← e.prod_comp]
  simp only [Equiv.symm_apply_apply]

theorem pi_restrict (j : A↪B) (μ : B→FiniteLaw X) (f : (A→X)→ℝ) :
    (FiniteLaw.pi μ).expect (fun ω => f (fun a => ω (j a))) =
      (FiniteLaw.pi (fun a => μ (j a))).expect f := by
  let Z := {b : B // b∉Set.range j}
  let e : A⊕Z ≃ B :=
    (Equiv.sumCongr (Equiv.ofInjective j j.injective) (Equiv.refl Z)).trans
      (Equiv.sumCompl (fun b => b∈Set.range j))
  have he (a : A) : e (.inl a)=j a := rfl
  rw [pi_relabel e]
  simp only [← he,Equiv.symm_apply_apply]
  rw [CanonicalExtensionLaw.pi_sum_expect]
  simp only [Sum.elim_inl,FiniteLaw.expect_const]
  have hdec : (inferInstance : DecidableEq A)=(fun a b => Classical.propDecidable (a=b)) :=
    Subsingleton.elim _ _
  cases hdec
  rfl

theorem complete_restrict_agrees (S D : Finset Site) (hSD : S⊆D)
    (ω : D→Bool) :
    Set.EqOn (complete ω) (complete (fun v : S => ω ⟨v,hSD v.property⟩)) S := by
  intro v hv
  change v∈S at hv
  simp only [complete,dite_eq_left hv,dite_eq_left (hSD hv)]

/-- Literal finite support restriction for arbitrary local two-replica tests. -/
theorem joint_expect_restrict (S D : Finset Site) (hSD : S⊆D)
    (t : ℝ) (ht : 0≤t) (F : Configuration→Configuration→ℝ)
    (hlocal : ∀ a b a' b',Set.EqOn a a' S → Set.EqOn b b' S → F a b=F a' b') :
    (jointLaw (fun _ : D => refreshProbability t)
      (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)).expect
      (fun ω => F (complete (fun v => (ω v).1)) (complete (fun v => (ω v).2))) =
    (jointLaw (fun _ : S => refreshProbability t)
      (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)).expect
      (fun ω => F (complete (fun v => (ω v).1)) (complete (fun v => (ω v).2))) := by
  let j : S↪D := ⟨fun v => ⟨v,hSD v.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun v : D => v.val) h)⟩
  have hp (ω : D→Bool×Bool) :
      F (complete (fun v => (ω v).1)) (complete (fun v => (ω v).2)) =
      F (complete (fun v => (ω (j v)).1)) (complete (fun v => (ω (j v)).2)) :=
    hlocal _ _ _ _ (complete_restrict_agrees S D hSD _) (complete_restrict_agrees S D hSD _)
  rw [FiniteLaw.expect_congr _ hp]
  exact pi_restrict j (fun _ => pairLaw (refreshProbability t)
    (refreshProbability_nonneg ht) (refreshProbability_le_one t))
    (fun ω => F (complete (fun v => (ω v).1)) (complete (fun v => (ω v).2)))

theorem jointProbability_restrict (S D : Finset Site) (hSD : S⊆D)
    (t : ℝ) (ht : 0≤t) (E : Configuration→Prop)
    (hlocal : ∀ ω η,Set.EqOn ω η S → (E ω ↔ E η)) :
    jointProbability D t E=jointProbability S t E := by
  rw [jointProbability_eq_law D t ht,jointProbability_eq_law S t ht]
  apply joint_expect_restrict S D hSD t ht (fun a b => indicator (E a ∧ E b))
  intro a b a' b' ha hb
  exact congrArg indicator (propext (and_congr (hlocal _ _ ha) (hlocal _ _ hb)))

#print axioms pi_restrict
#print axioms jointProbability_restrict

end
end ExceptionalTimes.IndependentSupportExtension
