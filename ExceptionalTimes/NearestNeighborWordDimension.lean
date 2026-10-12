import ExceptionalTimes.DyadicDimension
import ExceptionalTimes.QuadAnnulusTransfer
import ExceptionalTimes.LocalClockControl

/-! Literal rate-one nearest-neighbor model: the current final conditional
driver, with the finite crossing-word transfer premise exposed.
This is not yet the theorem conditional only on published results. -/

namespace ExceptionalTimes.NearestNeighborWordDimension

open MeasureTheory Set CanonicalEdgeIndex CanonicalBlockLaw PublishedPoissonConstruction
open PublishedExclusionUpper CanonicalEnergyFromProbeDecay OriginOneArmInputs
open AnnulusTransferMixing LocalAnnulusInput LocalDimerCalibration QuadAnnulusTransfer
open scoped ENNReal

theorem exists_realization_dimension_of_new_word_transfer
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
    (hindependent : PublishedIndependentLocalAnnulusMixing)
    (hplane : PairSquareSewing.PublishedInvarianceOfDomain)
    (happrox : StaticHexApproximation.PublishedHexQuadApproximation hplane)
    (B0 : ℝ) (hattach : PairSquareSewing.UnitStaticAttachment.PublishedUnitAttachment B0)
    (hpositive : PairSquareSewing.Source06Specialization.PublishedCircularArmLower B0)
    (hfour : UnitClockControl.PublishedDyadicFourArmLower B0)
    (htransfer : NewFiniteWordTransfer hplane) :
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
  · exact CalibratedAnnulusMixing.dyadic_mixing_of_new_transfer independentTime
      hindependent (localClock .canonical)
      (LocalClockControl.local_clock_control B0 hattach hpositive hfour .canonical)
      (annulus_transfer_of_words hplane happrox
        (LocalClockControl.local_clock_control B0 hattach hpositive hfour .canonical)
        (LocalClockControl.local_clock_control B0 hattach hpositive hfour .refresh) htransfer)

#print axioms exists_realization_dimension_of_new_word_transfer

end ExceptionalTimes.NearestNeighborWordDimension

