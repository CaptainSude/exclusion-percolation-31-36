import ExceptionalTimes.FixedAspectEnergy

/-! Concrete all-kernel dimension driver, reducing the entire new
probabilistic obligation to fixed-aspect canonical arm mixing. The
remaining premise is named NEW and is not a published result. -/

open MeasureTheory

namespace ExceptionalTimes.FixedAspectDimension

open CanonicalEdgeIndex CanonicalBlockLaw PublishedPoissonConstruction
open PublishedExclusionUpper CanonicalEnergyFromProbeDecay OriginOneArmInputs
open FixedAspectEnergy

theorem exists_realization_dimension_of_new_fixed_aspect_mixing
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
    (k : RateKernel) (hnew : ∀ z,0<k.rate z → NewFixedAspectMixing z) :
    ∃ (ν : Displacement → Measure PositiveMarks),
      (∀ z, IsProbabilityMeasure (ν z)) ∧
      ∃ P : PoissonGraphicalRealization (law ν) k.unorderedPairRate,
        P.initial = initial ∧
        Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
        Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
          (translateTrajectory (1,0)) ∧
        AlmostSureConjecturedDimension (law ν) P.trajectories := by
  apply ConcreteCanonicalDriver.exists_realization_dimension_of_new_canonical_energy
    hpoisson hgraphical hupper hcapacity k
  exact newCanonicalEnergy_of_new_probe_decay hboundary hJordan hRSW harm hβ
    hES hquasi hexponent k
    (fun z hz => scale_dependent_probe_decay_of_fixed_aspect horder z B₀ (hnew z hz))

#print axioms exists_realization_dimension_of_new_fixed_aspect_mixing

end ExceptionalTimes.FixedAspectDimension
