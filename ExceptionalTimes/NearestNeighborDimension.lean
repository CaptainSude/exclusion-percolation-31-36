import ExceptionalTimes.DyadicDimension
import ExceptionalTimes.AnnulusTransferMixing

/-! Literal rate-one nearest-neighbor model: the current final conditional
driver, with its TWO still-new transfer/calibration premises exposed.
This is not yet the theorem conditional only on published results. -/

namespace ExceptionalTimes.NearestNeighborDimension

open MeasureTheory Set CanonicalEdgeIndex CanonicalBlockLaw PublishedPoissonConstruction
open PublishedExclusionUpper CanonicalEnergyFromProbeDecay OriginOneArmInputs
open AnnulusTransferMixing IndependentAnnulusInput
open scoped ENNReal

theorem exists_realization_dimension_of_new_transfer
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
    (hindependent : PublishedIndependentAnnulusMixing)
    (J : ℕ→ℝ) (hclock : NewClockControl J) (htransfer : NewCenteredAnnulusTransfer J) :
    ∃ (ν : Displacement → Measure PositiveMarks),
      (∀ z, IsProbabilityMeasure (ν z)) ∧
      ∃ P : PoissonGraphicalRealization (law ν) NearestNeighborRates.kernel.unorderedPairRate,
        P.initial = initial ∧
        Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
        Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
          (translateTrajectory (1,0)) ∧
        AlmostSureConjecturedDimension (law ν) P.trajectories := by
  apply DyadicDimension.exists_realization_dimension_of_one_new_dyadic_fixed_aspect_mixing
    hpoisson hgraphical hupper hcapacity hboundary hJordan horder hRSW harm hβ hES
    hquasi hexponent NearestNeighborRates.kernel (1,0) (by decide)
  · change 0<NearestNeighborRates.rate (1,0)
    rw [NearestNeighborRates.rate_unit]
    norm_num
  · exact dyadic_mixing_of_new_transfer hindependent J hclock htransfer

#print axioms exists_realization_dimension_of_new_transfer

end ExceptionalTimes.NearestNeighborDimension
