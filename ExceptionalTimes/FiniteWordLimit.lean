import ExceptionalTimes.IndependentJointAssociation
import Mathlib.Topology.Algebra.Order.Field
import ExceptionalTimes.ExpansionLimit

/-! Finite-word decorrelation follows from coordinate cross-covariance
decay and the proved association inequality. State spaces may vary with
the limiting parameter. No independent-to-canonical transfer is assumed
to have been established by this lemma. -/

open scoped Classical BigOperators Topology

namespace ExceptionalTimes.FiniteWordMixing

open EnvironmentVariance Filter

theorem tendsto_word_covariance_zero {T : Type*} (l : Filter T)
    {Ω : T→Type*} [∀ t,Fintype (Ω t)]
    {I J : Type*} [Fintype I] [Fintype J]
    (μ : ∀ t,FiniteLaw (Ω t)) (X : ∀ t,Ω t→I→Bool) (Y : ∀ t,Ω t→J→Bool)
    (hassoc : ∀ t,∀ (f : (I→Bool)→ℝ) (g : (J→Bool)→ℝ),
      (∀ x,0≤f x) → (∀ y,0≤g y) → Monotone f → Monotone g →
      0≤covariance (μ t) (fun ω => f (X t ω)) (fun ω => g (Y t ω)))
    (hcoord : ∀ i j,Tendsto (fun t => covariance (μ t)
      (fun ω => bit (X t ω i)) (fun ω => bit (Y t ω j))) l (𝓝 0))
    (F : (I→Bool)→ℝ) (G : (J→Bool)→ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) (hG : ∀ y,0≤G y ∧ G y≤1) :
    Tendsto (fun t => covariance (μ t)
      (fun ω => F (X t ω)) (fun ω => G (Y t ω))) l (𝓝 0) := by
  have hsum : Tendsto (fun t => ∑ i,∑ j,covariance (μ t)
      (fun ω => bit (X t ω i)) (fun ω => bit (Y t ω j))) l (𝓝 0) := by
    have H := tendsto_finsetSum (Finset.univ : Finset I) (fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset J) (fun j _ => hcoord i j))
    simpa only [Finset.sum_const_zero] using H
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun t => word_covariance_le_sum (μ t) (X t) (Y t) (hassoc t) F G hF hG) hsum

#print axioms tendsto_word_covariance_zero

end ExceptionalTimes.FiniteWordMixing
