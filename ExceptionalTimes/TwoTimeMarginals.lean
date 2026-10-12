import ExceptionalTimes.IndependentAnnulusInput
import ExceptionalTimes.PairedEventTransfer
import ExceptionalTimes.FiniteSiteLaw

/-! Both actual two-time laws have exactly the same fair one-time law.
These identities apply to arbitrary events, including nonmonotone arm tests. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.TwoTimeMarginals

open EnvironmentVariance ProbeProduct IndependentJointAssociation ManyDimerLaw DimerLaw
open FiniteHaar ActivePartitionLaw PairSquareSewing

variable {B : Type*} [Fintype B]

theorem canonical_left (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (f : (B→Color)→ℝ) :
    (manyLaw p hp0 hp1).expect (fun ω => f ω.1)=average f := by
  simp only [FiniteLaw.expect,manyLaw,Fintype.sum_prod_type]
  rw [many_expect_replica p hp0 hp1]
  simp only [FiniteLaw.expect_const]
  exact many_marginal_expect p hp0 hp1 f

theorem canonical_right (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (f : (B→Color)→ℝ) :
    (manyLaw p hp0 hp1).expect (fun ω => f ω.2)=average f := by
  simp only [FiniteLaw.expect,manyLaw,Fintype.sum_prod_type]
  rw [many_expect_replica p hp0 hp1]
  simp only [FiniteLaw.expect_const]
  exact many_marginal_expect p hp0 hp1 f

def historyEquiv (V : Type*) : (V→Bool×Bool) ≃ ((V→Bool)×(V→Bool)) where
  toFun ω := (fun v => (ω v).1,fun v => (ω v).2)
  invFun ω := fun v => (ω.1 v,ω.2 v)
  left_inv _ := rfl
  right_inv _ := rfl

theorem pairWeight_row (p : ℝ) (a : Bool) : ∑ b : Bool,pairWeight p (a,b)=1/2 := by
  cases a <;> simp [pairWeight] <;> ring

theorem pairWeight_column (p : ℝ) (b : Bool) : ∑ a : Bool,pairWeight p (a,b)=1/2 := by
  cases b <;> simp [pairWeight] <;> ring

theorem independent_left {V : Type*} [Fintype V] [DecidableEq V]
    (p : V→ℝ) (hp0 : ∀ v,0≤p v) (hp1 : ∀ v,p v≤1) (f : (V→Bool)→ℝ) :
    (jointLaw p hp0 hp1).expect (fun ω => f (fun v => (ω v).1))=(fairSites V).expect f := by
  unfold FiniteLaw.expect
  rw [← (historyEquiv V).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ a : V→Bool,∑ b : V→Bool,(∏ v,pairWeight (p v) (a v,b v))*f a)=_
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul,← Fintype.prod_sum (fun v (b : Bool) => pairWeight (p v) (a v,b))]
  simp only [pairWeight_row,fairSites,FiniteLaw.pi,fairBit]

theorem independent_right {V : Type*} [Fintype V] [DecidableEq V]
    (p : V→ℝ) (hp0 : ∀ v,0≤p v) (hp1 : ∀ v,p v≤1) (f : (V→Bool)→ℝ) :
    (jointLaw p hp0 hp1).expect (fun ω => f (fun v => (ω v).2))=(fairSites V).expect f := by
  unfold FiniteLaw.expect
  rw [← (historyEquiv V).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ a : V→Bool,∑ b : V→Bool,(∏ v,pairWeight (p v) (a v,b v))*f b)=_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul,← Fintype.prod_sum (fun v (a : Bool) => pairWeight (p v) (a,b v))]
  simp only [pairWeight_column,fairSites,FiniteLaw.pi,fairBit]

#print axioms canonical_left
#print axioms independent_left
#print axioms independent_right

end ExceptionalTimes.TwoTimeMarginals
