import ExceptionalTimes.FixedAspectDimension

/-! A single positive-rate displacement suffices for the dimension
reduction. This avoids requiring a canonical estimate in every direction. -/

namespace ExceptionalTimes.SingleDisplacementDimension

open MeasureTheory Set KernelDimensionReduction
open scoped ENNReal
open FiniteMatchingExhaustion FiniteMatchingNormalization FiniteEdgeExhaustion

theorem almostSureConjecturedDimension_of_single_matching_energy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (k : RateKernel) (P : PoissonGraphicalRealization μ k.unorderedPairRate)
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (z : Site) (hz : z ≠ 0) (hpos : 0 < k.rate z)
    (hcanonical :
      CanonicalOneArmEnergyBound z (0,0) (FairOneArm.probability P))
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (shift : Site)
    (hshift : Function.Semiconj P.trajectories e (translateTrajectory shift))
    (hupper : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (P.trajectories ω)) ≤ (31 / 36 : ℝ≥0∞)) :
    AlmostSureConjecturedDimension μ P.trajectories := by
  have hpreserve := ClockClosurePreservation.ae_siteClosurePreservesPercolationAt_kernel k P (0,0)
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
    ?_ hstatQ hcanonical hpQ e he shift hshiftQ huQ
  intro R t
  exact FiniteClockMarginal.oneArm_marginal Q hr edges edges_monotone edges_exhaustive
    (0,0) R (FairOneArm.origin_mem_latticeBox R) t


#print axioms almostSureConjecturedDimension_of_single_matching_energy

open CanonicalEdgeIndex CanonicalBlockLaw PublishedPoissonConstruction
open PublishedExclusionUpper CanonicalEnergyFromProbeDecay OriginOneArmInputs
open FixedAspectEnergy

/-- The concrete process needs the new mixing estimate for only one
displacement whose exchange rate is positive. -/
theorem exists_realization_dimension_of_one_new_fixed_aspect_mixing
    (hpoisson : PositivePoissonMarks)
    (hgraphical : NormalizedGraphicalRegularity)
    (hupper : NormalizedDimensionUpper.{0})
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (hboundary : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PairSquareSewing.PublishedPolygonCrossingOrder)
    (horder : Annulus.PublishedAnnularCrosscutOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (harm : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β)
    (hES : ClassicalFiniteEfronStein)
    (hquasi : PublishedOriginQuasiMultiplicativity)
    (hexponent : PublishedOriginOneArmExponent)
    (k : RateKernel) (z : Site) (hz : z≠0) (hpos : 0<k.rate z)
    (hnew : NewFixedAspectMixing z) :
    ∃ (ν : Displacement → Measure PositiveMarks),
      (∀ z, IsProbabilityMeasure (ν z)) ∧
      ∃ P : PoissonGraphicalRealization (law ν) k.unorderedPairRate,
        P.initial = initial ∧
        Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
        Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
          (translateTrajectory (1,0)) ∧
        AlmostSureConjecturedDimension (law ν) P.trajectories := by
  obtain ⟨ν,hν,P,hi,he,hs⟩ := exists_canonical_realization hpoisson hgraphical k
  refine ⟨ν,hν,P,hi,he,hs,?_⟩
  apply almostSureConjecturedDimension_of_single_matching_energy k P hcapacity z hz hpos
    ?_ (ProductSpatialShift.translation (1,0)) he (1,0) hs (dimension_upper hupper k P)
  rw [ConcreteCanonicalDriver.probability_eq_finiteFairOneArm]
  exact canonical_energy_of_new_probe_decay hboundary hJordan hRSW harm hβ hES
    hquasi hexponent z hz (scale_dependent_probe_decay_of_fixed_aspect horder z B₀ hnew)

#print axioms exists_realization_dimension_of_one_new_fixed_aspect_mixing

end ExceptionalTimes.SingleDisplacementDimension

