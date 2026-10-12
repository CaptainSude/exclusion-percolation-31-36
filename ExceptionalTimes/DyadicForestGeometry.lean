import ExceptionalTimes.CircularForestGeometry
import ExceptionalTimes.DyadicForestEnvelope
import ExceptionalTimes.UnitClockControl

/-! The actual dyadic-box matching cover satisfies the selected geometry
bound, for both matching phases. Test support, microscopic margins and
every optimized stopping radius are discharged by deterministic geometry
and lattice counting. -/

open scoped Classical BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.DyadicForestGeometry
noncomputable section
open PairSquareSewing FixedMeshSelectedForest DimerSelectedDictionary
open DimerExpansion CenteredBlocks CanonicalSpatialProduct CircularStaticProfile
open ForestGeometryEnvelope WordForestGeometry SelectedPerturbation
open DyadicForestEnvelope IndependentAnnulusInput UnitReferenceCover Filter

variable {F : Type*} [Fintype F]

theorem geometryBound
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily F) (R n : ℕ) (hn : T.maxLevel≤n)
    (hsupport : testSupport hplane T n⊆sites R n) (phase : Bool)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (hcut : B*mesh n≤T.stop) (outer : (F×Bool→Bool)→ℝ) (hf : ∀ x,|outer x|≤1) :
    GeometryBound (fun _ => ActualProductTransfer.baseLaw)
      (fun h => outer (fun qt => T.test n qt.1
        (canonicalBackground (slot phase (sites R n)) (pairCoordinates.symm h) qt.2)))
      (value hplane T R phase B C₄ C₃ Q c g n) := by
  have hm : mesh n≤1 := by
    unfold mesh
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hr : mesh n≤ballRadius R := by unfold ballRadius; nlinarith [Nat.cast_nonneg (α := ℝ) R]
  apply CircularForestGeometry.circular_envelope_geometryBound hplane hbulk hhalf T n hn
    (1,0) (slot phase (sites R n)) (slot_positive phase (sites R n))
    (fun v hv => slot_covers phase (sites R n) v (hsupport hv)) hcircle hthree hcC₃
    B T.stop (11*B*ballRadius R) le_rfl hcut (stop_four_lt_one T) le_rfl
  · intro S
    change (geometry hplane T R phase n S).margin≤(B*mesh n)/100
    rw [geometry_margin]
    nlinarith [hcircle.1,mesh_pos n]
  · intro S hS
    exact OptimizedForestStop.cutoff_le_radius (anchors phase (sites R n)) 0
      (mesh_pos n) hr (by linarith [hcircle.1]) hcut
      (anchor_bound R phase n) (by simpa only [Finset.one_le_card] using hS)
      (by simpa only [Fintype.card_coe] using Finset.card_le_univ S)
  · exact hf

theorem value_nonneg
    (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R n : ℕ) (phase : Bool)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hcut : B*mesh n≤T.stop) (S : Finset (Blocks R phase n)) :
    0≤value hplane T R phase B C₄ C₃ Q c g n S :=
  envelope_nonneg _ _ _ _ _ _ _ _
    (profile_pos hcircle (mesh n) (mesh_pos n) T.stop hcut (stop_four_lt_one T)) S

theorem eventually_geometryBound
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily F) (R : ℕ)
    (hsupport : ∀ n,testSupport hplane T n⊆sites R n)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (outer : (F×Bool→Bool)→ℝ) (hf : ∀ x,|outer x|≤1) :
    ∀ᶠ n in atTop,∀ phase : Bool,
      GeometryBound (fun _ => ActualProductTransfer.baseLaw)
        (fun h => outer (fun qt => T.test n qt.1
          (canonicalBackground (slot phase (sites R n)) (pairCoordinates.symm h) qt.2)))
        (value hplane T R phase B C₄ C₃ Q c g n) ∧
      ∀ S,0≤value hplane T R phase B C₄ C₃ Q c g n S := by
  have hB : 0<B := by linarith [hcircle.1]
  have hsmall : 0<T.stop/B := div_pos T.stop_pos hB
  filter_upwards [UnitClockControl.mesh_tendsto_zero.eventually (gt_mem_nhds hsmall),
    eventually_ge_atTop T.maxLevel] with n hmesh hn
  have hcut : B*mesh n≤T.stop := by
    have hh := (lt_div_iff₀ hB).mp hmesh
    nlinarith
  intro phase
  exact ⟨geometryBound hplane hbulk hhalf T R n hn (hsupport n) phase hcircle hthree
    hcC₃ hcut outer hf,fun S => value_nonneg hplane T R n phase hcircle hcut S⟩

theorem exists_word_geometryBound {q : ℕ}
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily (Fin q)) (word : (Fin q→Bool)→Bool)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃) :
    ∃ R : ℕ,1≤R ∧ (∀ n,testSupport hplane T n⊆sites R n) ∧
      ∀ᶠ n in atTop,∀ phase : Bool,
        GeometryBound (fun _ => ActualProductTransfer.baseLaw)
          (DimerProbabilityDictionary.pairedTest (slot phase (sites R n))
            (StaticHexApproximation.wordEvent T n word))
          (value hplane T R phase B C₄ C₃ Q c g n) ∧
        ∀ S,0≤value hplane T R phase B C₄ C₃ Q c g n S := by
  obtain ⟨R,hR,hsupport,_⟩ := Source06Specialization.dyadic_support_and_anchors T hplane
  refine ⟨R,hR,hsupport,?_⟩
  simpa only [wordOuter_pairedTest] using eventually_geometryBound hplane hbulk hhalf T R
    hsupport hcircle hthree hcC₃ (wordOuter word) (wordOuter_abs_le_one word)

#print axioms exists_word_geometryBound
end
end ExceptionalTimes.DyadicForestGeometry
