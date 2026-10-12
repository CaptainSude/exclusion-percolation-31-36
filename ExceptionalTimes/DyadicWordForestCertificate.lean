import ExceptionalTimes.DyadicForestMass
import ExceptionalTimes.DyadicForestGeometry
import ExceptionalTimes.WordForestCertificate
import ExceptionalTimes.SourceCalibrationSampling
import ExceptionalTimes.DyadicDegreeConvergence

/-! Assembly of the concrete positive-cover forest certificate. The final
degree limit is supplied by the separate ordered sewing integration. -/
open Filter
open scoped Classical BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.DyadicWordForestCertificate
noncomputable section
open PairSquareSewing Source06Specialization CircularStaticProfile
open DyadicForestEnvelope WordProductBridge WordForestCertificate
open EffectiveDimerInsertion FixedMeshSelectedForest WordForestGeometry

theorem circular_lower {B C₄ Q c g : ℝ}
    (h : PublishedCircularArmInputs B C₄ Q c g) : PublishedCircularArmLower B := by
  refine ⟨h.1,c,h.2.2.2.1,g,h.2.2.2.2.1,?_⟩
  intro e he r hr hsmall hcut
  simpa only [cost_eq e he r hr hsmall] using input_cost_lower h e he r hcut hr hsmall

theorem data_of_degree {q : ℕ}
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily (Fin q)) (word : (Fin q→Bool)→Bool)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (hdegree : ∀R : ℕ,(∀n,testSupport hplane T n⊆sites R n)→
      ∀phase : Bool,∀k,Tendsto (fun n =>
        scaledCoefficient .canonical (wordTest T word (sites R n) phase n) (localScale .canonical n) k-
        scaledCoefficient .refresh (wordTest T word (sites R n) phase n) (localScale .refresh n) k)
        atTop (𝓝 0)) : Nonempty (Data hplane T word) := by
  obtain ⟨R,_hR,hsupport,hgeometry⟩ := DyadicForestGeometry.exists_word_geometryBound
    hplane hbulk hhalf T word hcircle hthree hcC₃
  obtain ⟨A,hA,hmass⟩ := DyadicForestMass.uniform_mass hplane T R (C₃:=C₃) hcircle hattach
  have hβ : 0<1-g/2 := by linarith [hcircle.2.2.2.2.2.1]
  exact ⟨{
    sites := sites R
    support := Filter.Eventually.of_forall hsupport
    G := fun phase n => value hplane T R phase B C₄ C₃ Q c g n
    A := A
    β := 1-g/2
    A_nonneg := hA
    β_pos := hβ
    geometry := fun phase => hgeometry.mono (fun _ hn => hn phase)
    mass := hmass
    degree := hdegree R hsupport
  }⟩

#print axioms circular_lower
#print axioms data_of_degree

theorem data {q : ℕ}
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily (Fin q)) (word : (Fin q→Bool)→Bool)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hlower : PublishedReferenceSquareLower) : Nonempty (Data hplane T word) := by
  apply data_of_degree hplane hbulk hhalf T word hcircle hthree hcC₃ hattach
  intro R hsupport phase
  exact DyadicDegreeConvergence.word_degree hplane T R phase hsupport hcircle hthree hcC₃
    hseams hstatic hbulk hhalf hlower (circular_lower hcircle) hattach word

#print axioms data

theorem data_without_constant_comparison {q : ℕ}
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily (Fin q)) (word : (Fin q→Bool)→Bool)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hlower : PublishedReferenceSquareLower) : Nonempty (Data hplane T word) := by
  have hthree' : PublishedHalfThreeArmBound B (max c C₃) := by
    intro P D hcut hcover
    exact (hthree P D hcut hcover).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  exact data hplane hbulk hhalf T word hcircle hthree' (le_max_left _ _)
    hattach hseams hstatic hlower

#print axioms data_without_constant_comparison
end
end ExceptionalTimes.DyadicWordForestCertificate
