import ExceptionalTimes.MixedCanonicalLaw
import ExceptionalTimes.MixedEnvironmentVariance

/-! The literal mixed canonical law is represented by conditional iid
replicas with freshly sampled exterior colors. Its grouped variance
therefore sums only over active mesoscopic cells. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedCanonicalVariance

noncomputable section

open FiniteHaar DimerLaw ManyDimerLaw EnvironmentVariance
open MixedCanonicalLaw MixedEnvironmentVariance GroupedDimerLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B O : Type*} [Fintype B] [Fintype O]

def uniformColors (O : Type*) [Fintype O] : FiniteLaw (O → Color) where
  weight _ := (Fintype.card (O → Color) : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem uniformColors_expect (f : (O → Color) → ℝ) :
    (uniformColors O).expect f = average f := by
  exact (Finset.mul_sum _ _ _).symm

def mixedReplica (e : B → Environment) : FiniteLaw ((B → Color) × (O → Color)) :=
  (manyReplica e).prod (uniformColors O)

theorem replica_probability (E : ((B → Color) × (O → Color)) → Prop)
    (e : B → Environment) :
    probability (mixedReplica (O := O) e) E =
      (manyReplica e).expect (smooth (fun x => indicator (E x))) := by
  unfold probability mixedReplica
  rw [FiniteLaw.expect_prod]
  apply FiniteLaw.expect_congr
  intro a
  exact uniformColors_expect _

theorem mixedProbability_eq_paired (p : B → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : ((B → Color) × (O → Color)) → Prop) :
    mixedProbability p E =
      pairedProbability (manyEnvironment p hp0 hp1) (mixedReplica (O := O)) E := by
  rw [mixedProbability, mixed_eq_environment_square p hp0 hp1, pairedProbability_eq]
  simp only [replica_probability]

theorem mixed_marginal (p : B → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : ((B → Color) × (O → Color)) → Prop) :
    marginalProbability (manyEnvironment p hp0 hp1) (mixedReplica (O := O)) E =
      average (smooth (fun x => indicator (E x))) := by
  unfold marginalProbability
  simp only [replica_probability]
  exact many_marginal_expect p hp0 hp1 _

variable {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]

local instance : DecidableEq (Sigma J) := fun a b => Classical.propDecidable (a = b)

/-- This is the grouped variance bound for the actual mixed law. Only
active dimer groups are resampled in Efron--Stein; exterior colors are
independent in each replica and contribute no pivotal summand. -/
theorem mixed_dimer_variance
    (p : Sigma J → ℝ) (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (E : ((Sigma J → Color) × (O → Color)) → Prop)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun j => environmentLaw (p ⟨i,j⟩) (hp0 ⟨i,j⟩) (hp1 ⟨i,j⟩)))) :
    mixedProbability p E - (average (smooth (fun x => indicator (E x)))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i,
        mixedProbability p (activeGroupPivotal (S := fun _ _ => Color) E i) := by
  rw [← mixed_marginal p hp0 hp1 E]
  simp_rw [mixedProbability_eq_paired p hp0 hp1]
  exact mixed_nested_variance
    (fun i j => environmentLaw (p ⟨i,j⟩) (hp0 ⟨i,j⟩) (hp1 ⟨i,j⟩))
    (fun _ _ => replicaLaw) (uniformColors O) E hES

#print axioms mixedProbability_eq_paired
#print axioms mixed_dimer_variance

end

end ExceptionalTimes.MixedCanonicalVariance
