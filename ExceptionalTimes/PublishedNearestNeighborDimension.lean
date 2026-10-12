import ExceptionalTimes.NearestNeighborWordDimension
import ExceptionalTimes.DyadicWordForestCertificate

/-! The rate-one nearest-neighbor 31/36 theorem, conditional on the named
literature inputs. The new finite-word transfer, local clock control,
forest integration, coefficient sewing and semigroup comparison are
proved internally. Source correspondence of the named published inputs
is documented separately in the assumption ledger. -/
namespace ExceptionalTimes.PublishedNearestNeighborDimension

open MeasureTheory Set CanonicalEdgeIndex CanonicalBlockLaw PublishedPoissonConstruction
open PublishedExclusionUpper CanonicalEnergyFromProbeDecay OriginOneArmInputs
open PairSquareSewing Source06Specialization CircularStaticProfile
open AnnulusTransferMixing LocalAnnulusInput LocalDimerCalibration
open scoped ENNReal

theorem exists_realization_dimension
    (hpoisson : PositivePoissonMarks)
    (hgraphical : NormalizedGraphicalRegularity)
    (hupper : NormalizedDimensionUpper.{0})
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (hboundary : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PublishedPolygonCrossingOrder)
    (horder : Annulus.PublishedAnnularCrosscutOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (harm : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β)
    (hES : ClassicalFiniteEfronStein)
    (hquasi : PublishedOriginQuasiMultiplicativity)
    (hexponent : PublishedOriginOneArmExponent)
    (hindependent : PublishedIndependentLocalAnnulusMixing)
    (hplane : PublishedInvarianceOfDomain)
    (happrox : StaticHexApproximation.PublishedHexQuadApproximation hplane)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    {B C₄ C₃ Q c g : ℝ}
    (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (hfour : UnitClockControl.PublishedDyadicFourArmLower B)
    (hseams : PublishedFixedSquareSeams B)
    (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hlower : PublishedReferenceSquareLower) :
    ∃ (ν : Displacement → Measure PositiveMarks),
      (∀ z, IsProbabilityMeasure (ν z)) ∧
      ∃ P : PoissonGraphicalRealization (law ν) NearestNeighborRates.kernel.unorderedPairRate,
        P.initial = initial ∧
        Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
        Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
          (translateTrajectory (1,0)) ∧
        AlmostSureConjecturedDimension (law ν) P.trajectories := by
  have hpositive := DyadicWordForestCertificate.circular_lower hcircle
  have hclock (rule : Rule) : NewClockControl (localClock rule) :=
    LocalClockControl.local_clock_control B hattach hpositive hfour rule
  have htransfer : QuadAnnulusTransfer.NewFiniteWordTransfer hplane :=
    WordForestCertificate.transfer_of_data hplane hclock
      (fun _ T word => DyadicWordForestCertificate.data_without_constant_comparison hplane hbulk hhalf T word
        hcircle hthree hattach hseams hstatic hlower)
  exact NearestNeighborWordDimension.exists_realization_dimension_of_new_word_transfer
    hpoisson hgraphical hupper hcapacity hboundary hJordan horder hRSW harm hβ hES
    hquasi hexponent hindependent hplane happrox B hattach hpositive hfour htransfer

#print axioms exists_realization_dimension
end ExceptionalTimes.PublishedNearestNeighborDimension

