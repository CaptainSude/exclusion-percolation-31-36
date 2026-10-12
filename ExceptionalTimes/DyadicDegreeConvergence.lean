import ExceptionalTimes.OrderedDegreeLimit
import ExceptionalTimes.DyadicNormalizedForest
import ExceptionalTimes.DimerDegreeZero

/-! Actual fixed-degree coefficient convergence under the explicitly
named ordinary static and OpenAI sewing inputs. Both the good-tuple
comparison and the bad-tuple forest domination are instantiated. -/
open Filter
open scoped Classical BigOperators Topology
namespace ExceptionalTimes.DyadicDegreeConvergence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PairSquareSewing Source06Specialization IndependentAnnulusInput
open LocalDimerCalibration InsertionCounting OrderedDimerCoefficients
open FixedMeshSelectedForest UnitReferenceCover OrderedGoodSewing
open ForestSelectionIntegral EffectiveDimerInsertion
open CanonicalSpatialProduct DimerExpansion CircularStaticProfile

theorem positive_degree {q k : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R : ℕ) (phase : Bool)
    (hsupport : ∀n,testSupport hplane T n⊆DyadicForestEnvelope.sites R n)
    {B C₄ C₃ Q c g : ℝ}
    (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (hseams : PublishedFixedSquareSeams B)
    (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (hlower : PublishedReferenceSquareLower) (harmlower : PublishedCircularArmLower B)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (outer : (Fin q×Bool→Bool)→ℝ) (hout : ∀x,|outer x|≤1) :
    Tendsto (fun n =>
      scaledCoefficient .canonical
        (fun h => outer (fun qt => T.test n qt.1
          (canonicalBackground (slot phase (box R n)) (pairCoordinates.symm h) qt.2)))
        ((mesh n)^2/localS .canonical n) (k+1)-
      scaledCoefficient .refresh
        (fun h => outer (fun qt => T.test n qt.1
          (canonicalBackground (slot phase (box R n)) (pairCoordinates.symm h) qt.2)))
        ((mesh n)^2/localS .refresh n) (k+1)) atTop (𝓝 0) := by
  obtain ⟨W,hW,hbound⟩ := DyadicNormalizedForest.eventual_ordered_bound hplane hbulk hhalf
    T R hsupport hcircle hthree hcC₃ hattach outer hout (k+1) (by omega)
  have hB : 0<B := by linarith [hcircle.1]
  have hradius : 0<OptimizedForestStop.radius T.stop
      (11*B*DyadicForestEnvelope.ballRadius R) (k+1) :=
    OptimizedForestStop.radius_pos T.stop_pos
      (by have hr := DyadicForestEnvelope.ballRadius_pos R; positivity) (by omega)
  apply OrderedDegreeLimit.tendsto_of_forest_domination hplane T R phase hsupport B
    hseams hstatic hbulk hlower harmlower hattach outer hout (fun n => B*mesh n)
    hB hcircle.2.2.2.2.1 hcircle.2.2.2.2.2.1 hradius
    (show 0≤max 1 (Q/c) by exact (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _))
    (show 0≤2*W by positivity) (Filter.Eventually.of_forall (fun _ => le_rfl))
  filter_upwards [hbound] with n hn
  intro o
  have hc := hn phase .canonical o
  have hm := hn phase .refresh o
  change |normalizedTerm hplane T R phase (k+1) n .canonical outer o|≤_ at hc
  change |normalizedTerm hplane T R phase (k+1) n .refresh outer o|≤_ at hm
  simpa only [←two_mul,mul_assoc,anchorSet,box,DyadicForestEnvelope.sites] using add_le_add hc hm

#print axioms positive_degree

theorem word_degree {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R : ℕ) (phase : Bool)
    (hsupport : ∀n,testSupport hplane T n⊆DyadicForestEnvelope.sites R n)
    {B C₄ C₃ Q c g : ℝ}
    (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (hseams : PublishedFixedSquareSeams B)
    (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (hlower : PublishedReferenceSquareLower) (harmlower : PublishedCircularArmLower B)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (word : (Fin q→Bool)→Bool) :
    ∀k : ℕ,Tendsto (fun n =>
      scaledCoefficient .canonical (WordProductBridge.wordTest T word
        (DyadicForestEnvelope.sites R n) phase n) (WordProductBridge.localScale .canonical n) k-
      scaledCoefficient .refresh (WordProductBridge.wordTest T word
        (DyadicForestEnvelope.sites R n) phase n) (WordProductBridge.localScale .refresh n) k)
      atTop (𝓝 0) := by
  intro k
  cases k with
  | zero =>
    simp only [DimerDegreeZero.difference_eq_zero]
    exact tendsto_const_nhds
  | succ k =>
    exact positive_degree hplane T R phase hsupport hcircle hthree hcC₃ hseams hstatic
      hbulk hhalf hlower harmlower hattach (WordForestGeometry.wordOuter word)
      (WordForestGeometry.wordOuter_abs_le_one word)

#print axioms word_degree
end
end ExceptionalTimes.DyadicDegreeConvergence
