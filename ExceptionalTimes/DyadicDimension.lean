import ExceptionalTimes.SingleDisplacementDimension
import ExceptionalTimes.DyadicFixedAspectEnergy
import ExceptionalTimes.NearestNeighborRates

/-! The complete dimension implication needs new fixed-aspect mixing only
on dyadic spatial scales, and only for one positive-rate displacement. -/

namespace ExceptionalTimes.DyadicDimension

open MeasureTheory Set KernelDimensionReduction
open scoped ENNReal
open FiniteMatchingExhaustion FiniteMatchingNormalization FiniteEdgeExhaustion
open CanonicalEdgeIndex CanonicalBlockLaw PublishedPoissonConstruction
open PublishedExclusionUpper CanonicalEnergyFromProbeDecay OriginOneArmInputs
open DyadicFixedAspectEnergy SingleDisplacementDimension

/-- The concrete process needs the new mixing estimate for only one
displacement whose exchange rate is positive. -/
theorem exists_realization_dimension_of_one_new_dyadic_fixed_aspect_mixing
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
    (hnew : NewDyadicFixedAspectMixing z) :
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
    hquasi hexponent z hz (scale_dependent_probe_decay_of_dyadic_fixed_aspect horder z B₀ hnew)

#print axioms exists_realization_dimension_of_one_new_dyadic_fixed_aspect_mixing

end ExceptionalTimes.DyadicDimension


