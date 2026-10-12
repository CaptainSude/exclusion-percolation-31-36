import ExceptionalTimes.MixedCanonicalVariance
import ExceptionalTimes.CanonicalProbeSupport

/-! Exact identification of the two-coordinate canonical replica law
with the original law on all dimer labels. The dictionary holds for
arbitrary real tests, including nonmonotone alternating-arm events. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedCanonicalDictionary

noncomputable section

open FiniteHaar DimerLaw ManyDimerLaw EnvironmentVariance
open MixedCanonicalLaw CanonicalProbeSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A O : Type*} [Fintype A] [Fintype O]

local instance : DecidableEq (A ⊕ O) := fun a b => Classical.propDecidable (a = b)

theorem expect_sum {B C : Type*} [Fintype B] [Fintype C]
    (μ : FiniteLaw B) (f : B → C → ℝ) :
    μ.expect (fun b => ∑ c, f b c) = ∑ c, μ.expect (fun b => f b c) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem bothCanonical_eq_joint (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (F : ((A → Color) × (O → Color)) → ℝ) :
    bothCanonical p q hp0 hp1 hq0 hq1 F =
      ∑ a, ∑ b, manyWeight p a b *
        (∑ o, ∑ v, manyWeight q o v * (F (a,o) * F (b,v))) := by
  symm
  have hq (a b : A → Color) :
      (∑ o, ∑ v, manyWeight q o v * (F (a,o) * F (b,v))) =
      (manyEnvironment q hq0 hq1).expect (fun d =>
        (manyReplica d).expect (fun o => F (a,o)) *
          (manyReplica d).expect (fun v => F (b,v))) := by
    rw [many_expect_replica q hq0 hq1]
    simp only [FiniteLaw.expect_const_mul, FiniteLaw.expect_mul_const]
  simp_rw [hq]
  calc
    _ = (manyEnvironment q hq0 hq1).expect (fun d =>
        ∑ a, ∑ b, manyWeight p a b *
          ((manyReplica d).expect (fun o => F (a,o)) *
            (manyReplica d).expect (fun v => F (b,v)))) := by
      simp only [expect_sum, FiniteLaw.expect_const_mul]
    _ = (manyEnvironment q hq0 hq1).expect (fun d =>
        (manyEnvironment p hp0 hp1).expect (fun e =>
          ((manyReplica e).expect (fun a => (manyReplica d).expect (fun o => F (a,o))))^2)) := by
      apply FiniteLaw.expect_congr
      intro d
      rw [many_expect_replica p hp0 hp1]
      simp only [FiniteLaw.expect_const_mul,FiniteLaw.expect_mul_const,pow_two]
    _ = _ := FiniteLaw.expect_comm _ _ _

theorem bothCanonical_eq_sum_law (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (F : ((A → Color) × (O → Color)) → ℝ) :
    bothCanonical p q hp0 hp1 hq0 hq1 F =
      (manyLaw (Sum.elim p q) (by intro s; cases s <;> simp_all)
        (by intro s; cases s <;> simp_all)).expect (fun z =>
          F (fun a => z.1 (.inl a),fun o => z.1 (.inr o)) *
            F (fun a => z.2 (.inl a),fun o => z.2 (.inr o))) := by
  rw [bothCanonical_eq_joint, sum_expect, FiniteLaw.expect_prod]
  simp only [FiniteLaw.expect, manyLaw, Fintype.sum_prod_type, sumLayers,
    Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr]

/-- The both-canonical event law is the actual full-dimer probability,
under the explicit sum partition of labels. -/
theorem bothCanonical_indicator_eq_manyProbability (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (E : ((A → Color) × (O → Color)) → Prop) :
    bothCanonical p q hp0 hp1 hq0 hq1 (fun x => indicator (E x)) =
      manyProbability (Sum.elim p q)
        (fun x => E (fun a => x (.inl a),fun o => x (.inr o))) := by
  rw [bothCanonical_eq_sum_law]
  simp only [FiniteLaw.expect,manyLaw,Fintype.sum_prod_type,manyProbability]

#print axioms bothCanonical_eq_sum_law
#print axioms bothCanonical_indicator_eq_manyProbability

end

end ExceptionalTimes.MixedCanonicalDictionary
