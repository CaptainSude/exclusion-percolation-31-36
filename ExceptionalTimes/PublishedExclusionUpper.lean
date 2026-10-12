import ExceptionalTimes.StochasticModel

/-! Garban--Vanneuville, Proposition 3.3, arXiv:1605.04766v3, page 19
(journal version, page 21), supplies the upper bound for every symmetric
transition matrix on triangular-lattice sites at density one-half.

The input below retains the transition-matrix normalization. Its process
is the literal independent unordered-pair clock construction, with fair
initial colors, encoded by PoissonGraphicalRealization. The theorem after
the input proves the adapter for arbitrary summable positive-mass kernels
by scaling their actual clock marks. No lower bound or canonical matching
energy estimate is included in this published input.

Source: https://arxiv.org/pdf/1605.04766v3#page=19
-/

open MeasureTheory
open scoped ENNReal

universe u

namespace ExceptionalTimes.PublishedExclusionUpper

def NormalizedDimensionUpper : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω)
    (k : RateKernel), k.mass = 1 →
      ∀ P : PoissonGraphicalRealization μ k.unorderedPairRate,
        ∀ᵐ ω ∂μ, dimH (exceptionalTimes (P.trajectories ω)) ≤ (31/36 : ℝ≥0∞)

theorem dimH_exceptional_rescale (X : Trajectory) {c : ℝ} (hc : 0 < c) :
    dimH (exceptionalTimes (rescaleTime c X)) = dimH (exceptionalTimes X) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have heq : exceptionalTimes (rescaleTime c X) = e ⁻¹' exceptionalTimes X := by
    ext t
    change (0 ≤ t ∧ HasInfiniteBlackCluster (X (c*t))) ↔
      (0 ≤ c*t ∧ HasInfiniteBlackCluster (X (c*t)))
    rw [mul_nonneg_iff_of_pos_left hc]
  rw [heq,e.dimH_preimage]

theorem normalized_unordered_rate (k : RateKernel) :
    (fun e => (1/k.mass) * k.unorderedPairRate e) = k.normalized.unorderedPairRate := by
  funext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    change (1/k.mass) * k.rate (v-u) = k.rate (v-u) / k.mass
    ring

theorem dimension_upper (hpublished : NormalizedDimensionUpper.{u})
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    (k : RateKernel) (P : PoissonGraphicalRealization μ k.unorderedPairRate) :
    ∀ᵐ ω ∂μ, dimH (exceptionalTimes (P.trajectories ω)) ≤ (31/36 : ℝ≥0∞) := by
  have hc : 0 < 1/k.mass := one_div_pos.mpr k.mass_pos
  have H : ∀ Q : PoissonGraphicalRealization μ
      (fun e => (1/k.mass) * k.unorderedPairRate e),
      ∀ᵐ ω ∂μ, dimH (exceptionalTimes (Q.trajectories ω)) ≤ (31/36 : ℝ≥0∞) := by
    rw [normalized_unordered_rate]
    exact hpublished Ω μ k.normalized k.normalized_mass
  apply (H (P.speedup (1/k.mass) hc)).mono
  intro ω hω
  simpa only [P.speedup_trajectories,dimH_exceptional_rescale _ hc] using hω

#print axioms dimension_upper

end ExceptionalTimes.PublishedExclusionUpper
