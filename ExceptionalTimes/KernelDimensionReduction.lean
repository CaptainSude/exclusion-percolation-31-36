import ExceptionalTimes.CanonicalEnergyDimension
import ExceptionalTimes.FiniteMatchingNormalization
import ExceptionalTimes.FiniteClockMarginal
import ExceptionalTimes.ClockStationarity
import ExceptionalTimes.ClockJointMeasurability
import ExceptionalTimes.ClockClosurePreservation

/-! The actual general-kernel dimension target follows from the explicit
canonical matching energy estimate. That estimate remains NEW and UNPROVED;
this reduction must not be described as a published-input-only certificate. -/

namespace ExceptionalTimes.KernelDimensionReduction

open MeasureTheory Set
open scoped ENNReal
open FiniteMatchingExhaustion FiniteMatchingNormalization FiniteEdgeExhaustion

theorem dimH_exceptional_rescale (X : Trajectory) {c : ℝ} (hc : 0 < c) :
    dimH (exceptionalTimes (rescaleTime c X)) = dimH (exceptionalTimes X) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have heq : exceptionalTimes (rescaleTime c X) = e ⁻¹' exceptionalTimes X := by
    ext t
    change (0 ≤ t ∧ HasInfiniteBlackCluster (X (c*t))) ↔
      (0 ≤ c*t ∧ HasInfiniteBlackCluster (X (c*t)))
    rw [mul_nonneg_iff_of_pos_left hc]
  rw [heq, e.dimH_preimage]

theorem almostSureConjecturedDimension_of_matching_energy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (k : RateKernel) (P : PoissonGraphicalRealization μ k.unorderedPairRate)
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (hcanonical : ∀ z : Site, 0 < k.rate z →
      CanonicalOneArmEnergyBound z (0,0) (FairOneArm.probability P))
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (shift : Site)
    (hshift : Function.Semiconj P.trajectories e (translateTrajectory shift))
    (hupper : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (P.trajectories ω)) ≤ (31 / 36 : ℝ≥0∞)) :
    AlmostSureConjecturedDimension μ P.trajectories := by
  have hpreserve := ClockClosurePreservation.ae_siteClosurePreservesPercolationAt_kernel k P (0,0)
  obtain ⟨z, hz, hpos⟩ := k.exists_positive_displacement
  let c : ℝ := 1 / (2 * k.rate z)
  have hc : 0 < c := by dsimp [c]; positivity
  let Q := P.speedup c hc
  have hr : ∀ edge, 0 ≤ c * k.unorderedPairRate edge :=
    fun edge => mul_nonneg hc.le (unorderedPairRate_nonneg k edge)
  apply (almostSureConjecturedDimension_speedup_iff P c hc).mp
  have hXQ : Measurable (fun p : Ω × ℝ => Q.trajectories p.1 p.2) := by
    exact ClockJointMeasurability.measurable_trajectories Q edges edges_monotone edges_exhaustive
  have hstatQ : ∀ R s t, 0 ≤ s → 0 ≤ t →
      μ {ω | OneArm (Q.trajectories ω s) (0,0) R ∧ OneArm (Q.trajectories ω t) (0,0) R} =
        μ {ω | OneArm (Q.trajectories ω 0) (0,0) R ∧
          OneArm (Q.trajectories ω (dist s t)) (0,0) R} := by
    intro R s t hs ht
    exact ClockStationarity.oneArm_stationary Q hr edges edges_monotone edges_exhaustive
      (0,0) R (FairOneArm.origin_mem_latticeBox R) s t hs ht
  have hpQ : ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (Q.trajectories ω) (0,0) := by
    apply hpreserve.mono
    intro ω hω
    have H := AffineTimeWindows.percolation_closure_preserves_affineTime hω (a := 0) (le_refl 0) hc.le
    have haff : AffineTimeWindows.affineTime 0 c (P.trajectories ω) =
        rescaleTime c (P.trajectories ω) := by
      funext t
      simp only [AffineTimeWindows.affineTime, rescaleTime, zero_add]
    rw [haff] at H
    simpa only [Q, P.speedup_trajectories] using H
  have hshiftQ : Function.Semiconj Q.trajectories e (translateTrajectory shift) := by
    intro ω
    simp only [Q, P.speedup_trajectories]
    funext t v
    exact congrFun (congrFun (hshift ω) (c*t)) v
  have huQ : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (Q.trajectories ω)) ≤ (31/36 : ℝ≥0∞) := by
    apply hupper.mono
    intro ω hω
    simpa only [Q, P.speedup_trajectories, dimH_exceptional_rescale _ hc] using hω
  apply CanonicalEnergyDimension.almostSureConjecturedDimension_of_canonical_energy Q
    hcapacity hXQ z hz (matching_normalization k z hpos) hr
    (0,0) FairOneArm.origin_mem_latticeBox (FairOneArm.probability P)
    (fun R => ne_of_gt (FairOneArm.probability_pos P R)) (FairOneArm.probability_ne_top P)
    ?_ hstatQ (hcanonical z hpos) hpQ e he shift hshiftQ huQ
  intro R t
  exact FiniteClockMarginal.oneArm_marginal Q hr edges edges_monotone edges_exhaustive
    (0,0) R (FairOneArm.origin_mem_latticeBox R) t

end ExceptionalTimes.KernelDimensionReduction

#print axioms ExceptionalTimes.KernelDimensionReduction.almostSureConjecturedDimension_of_matching_energy

