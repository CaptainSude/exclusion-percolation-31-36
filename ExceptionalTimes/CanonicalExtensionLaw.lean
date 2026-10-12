import ExceptionalTimes.CanonicalSpatialProduct
import ExceptionalTimes.CanonicalRadialLaw

/-! Unused whole dimers integrate to one at every nonnegative time.
This is the positive-time extension law needed when finite quad
approximations require a larger observation support than the arm event. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.CanonicalExtensionLaw

noncomputable section

open EnvironmentVariance DimerLaw ManyDimerLaw CanonicalSpatialProduct

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]

local instance : DecidableEq (A⊕B) := fun a b => Classical.propDecidable (a=b)

theorem pi_sum_expect (μ : A⊕B → FiniteLaw X) (f : (A⊕B → X)→ℝ) :
    (FiniteLaw.pi μ).expect f=
      (FiniteLaw.pi (fun a => μ (.inl a))).expect (fun x =>
        (FiniteLaw.pi (fun b => μ (.inr b))).expect (fun y => f (Sum.elim x y))) := by
  unfold FiniteLaw.expect
  rw [← (Equiv.sumArrowEquivProdArrow A B X).symm.sum_comp]
  simp only [Fintype.sum_prod_type,FiniteLaw.pi,Fintype.prod_sum_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact mul_assoc _ _ _

theorem manyLaw_inl (p : A⊕B → ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (f : ((A→Color)×(A→Color))→ℝ) :
    (manyLaw p hp0 hp1).expect
      (fun ω => f (fun a => ω.1 (.inl a),fun a => ω.2 (.inl a)))=
      (manyLaw (fun a => p (.inl a)) (fun a => hp0 (.inl a))
        (fun a => hp1 (.inl a))).expect f := by
  rw [manyLaw_pi,pi_sum_expect]
  simp only [pairCoordinates,Equiv.coe_fn_symm_mk,Sum.elim_inl,FiniteLaw.expect_const]
  exact (manyLaw_pi (fun a => p (.inl a)) (fun a => hp0 (.inl a))
    (fun a => hp1 (.inl a)) f).symm

theorem manyProbability_inl (p : A⊕B → ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (E : (A→Color)→Prop) :
    manyProbability p (fun ω => E (fun a => ω (.inl a)))=
      manyProbability (fun a => p (.inl a)) E := by
  rw [manyProbability_eq_joint p hp0 hp1,
    manyProbability_eq_joint _ (fun a => hp0 (.inl a)) (fun a => hp1 (.inl a))]
  exact manyLaw_inl p hp0 hp1 (fun ω => indicator (E ω.1 ∧ E ω.2))

#print axioms manyProbability_inl

end
end ExceptionalTimes.CanonicalExtensionLaw
