import ExceptionalTimes.DyadicForestGeometry
import ExceptionalTimes.NormalizedSelectedForest
import ExceptionalTimes.OrderedDimerCoefficients
import ExceptionalTimes.LocalClockControl

/-! Every fixed-degree ordered insertion, with its literal local clock
normalization, is dominated by one common forest weight. The constant is
uniform in mesh, matching phase, insertion rule and anchor tuple. -/

open scoped Classical BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.DyadicNormalizedForest
noncomputable section
open PairSquareSewing Source06Specialization FixedMeshSelectedForest
open DimerExpansion CenteredBlocks CanonicalSpatialProduct CircularStaticProfile
open ForestGeometryEnvelope WordForestGeometry SelectedPerturbation
open DyadicForestEnvelope IndependentAnnulusInput UnitReferenceCover Filter
open LocalClockControl LocalDimerCalibration ForestSelectionIntegral CanonicalForestOrdered
open InsertionCounting EffectiveDimerInsertion OrderedDimerCoefficients

variable {F : Type*} [Fintype F]

theorem eventual_ordered_bound
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily F) (R : ℕ)
    (hsupport : ∀ n,testSupport hplane T n⊆sites R n)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (outer : (F×Bool→Bool)→ℝ) (hf : ∀ x,|outer x|≤1)
    (k : ℕ) (hk : 1≤k) :
    ∃ W : ℝ,0≤W ∧ ∀ᶠ n in atTop,∀ phase : Bool,∀ rule : Rule,
      ∀ o : OrderedSelections (Blocks R phase n) k,
      |fullCoefficient (testSupport hplane T n) (orderedEndpoint (slot phase (sites R n)) o)
        (fun _ => rule) (fun ξ => outer (fun qt => T.test n qt.1 (ξ qt.2)))/(localS rule n)^k|≤
        W*forestTuple k (anchors phase (sites R n)) (mesh n) (B*mesh n) g
          (OptimizedForestStop.radius T.stop (11*B*ballRadius R) k) (max 1 (Q/c))
          (T.root hplane) (anchorTuple o) := by
  have hB : 0<B := by linarith [hcircle.1]
  have hc : 0<c := hcircle.2.2.2.1
  have hg : 0<g := hcircle.2.2.2.2.1
  let C := max 1 (Q/c)
  let K := canonicalForestConstant F C₄ C₃ c C Q g
  let ρ := OptimizedForestStop.radius T.stop (11*B*ballRadius R) k
  have hρ : 0<ρ := OptimizedForestStop.radius_pos T.stop_pos
    (by have hh := ballRadius_pos R; positivity) hk
  have hρstop : ρ≤T.stop := OptimizedForestStop.radius_le_stop ..
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  let P := ((K*C^2*256^g)^2*Real.exp (g*(1+4/100)))*(C*T.stop^g)
  have hP : 0≤P := mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (mul_nonneg hC (Real.rpow_nonneg T.stop_pos.le _))
  obtain ⟨ca,hca,e0,he0,hloc⟩ := localS_lower B hattach
  let L := cutoffConstant B Q c g B T.stop/ca
  have hconst : 0≤cutoffConstant B Q c g B T.stop := by
    unfold cutoffConstant
    exact div_nonneg (mul_nonneg (div_nonneg (by linarith [hcircle.2.2.1]) hc.le)
      (Real.rpow_nonneg (div_nonneg hB.le hB.le) _))
      (mul_nonneg hc.le (Real.rpow_nonneg T.stop_pos.le _))
  have hL : 0≤L := div_nonneg hconst hca.le
  refine ⟨(P*L)^k*ρ^(-g*(k:ℝ)),by positivity,?_⟩
  have hsmall : 0<min e0 (ρ/B) := lt_min he0 (div_pos hρ hB)
  filter_upwards [DyadicForestGeometry.eventually_geometryBound hplane hbulk hhalf T R
      hsupport hcircle hthree hcC₃ outer hf,
    UnitClockControl.mesh_tendsto_zero.eventually (gt_mem_nhds hsmall),
    eventually_ge_atTop T.maxLevel] with n hG hn hnlevel
  have he0n : mesh n<e0 := hn.trans_le (min_le_left _ _)
  have hcutρ : B*mesh n≤ρ := by
    have hh := (lt_div_iff₀ hB).mp (hn.trans_le (min_le_right _ _))
    nlinarith
  have hcut := hcutρ.trans hρstop
  have hstop1 := stop_four_lt_one T
  have hsmallarm : 4*(B*mesh n)<1 := lt_of_le_of_lt (by linarith) hstop1
  let p := profile (mesh n) (mesh_pos n) B T.stop
  have hp : ∀t,0<p t := profile_pos hcircle (mesh n) (mesh_pos n) T.stop hcut hstop1
  have hpstop : p T.stop=1 := profile_at_stop hcircle (mesh n) (mesh_pos n) T.stop hcut hstop1
  have hgrowth := profile_growth hcircle (mesh n) (mesh_pos n) T.stop hcut hstop1
  have hcal := profile_cutoff_le_sourceArmCost hcircle (mesh n) (mesh_pos n) T.stop B
    le_rfl hcut hstop1 hB hsmallarm
  have harm : 0<sourceArmCost (mesh n) (B*mesh n) (mesh_pos n)
      (mul_pos hB (mesh_pos n)) hsmallarm := by
    rw [←cost_eq (mesh n) (mesh_pos n) (B*mesh n) (mul_pos hB (mesh_pos n)) hsmallarm]
    exact input_cost_pos hcircle (mesh n) (mesh_pos n) (B*mesh n) le_rfl
      (mul_pos hB (mesh_pos n)) hsmallarm
  intro phase rule o
  have hlocal := hloc n he0n hB hsmallarm rule
  have hS : 0<localS rule n := (mul_pos hca harm).trans_le hlocal
  have hprofileCal : p (B*mesh n)≤L*localS rule n := by
    apply hcal.trans
    have hh := mul_le_mul_of_nonneg_left hlocal (div_nonneg hconst hca.le)
    have heq (a : ℝ) : (cutoffConstant B Q c g B T.stop/ca)*(ca*a)=
        cutoffConstant B Q c g B T.stop*a := by field_simp [hca.ne']
    rw [heq] at hh
    exact hh
  have hPb (S : Finset (Blocks R phase n)) :
      prefactor (geometry hplane T R phase n S) (B*mesh n) T.stop C K g≤P := by
    apply prefactor_le _ (mul_pos hB (mesh_pos n)) T.stop_pos.le hC hg.le
    rw [geometry_margin]
    nlinarith [hcircle.1,mesh_pos n]
  have hh := NormalizedSelectedForest.selected_ordered_bound
    (anchors phase (sites R n)) (Function.Embedding.refl _)
    (geometry hplane T R phase n)
    (fun h => outer (fun qt => T.test n qt.1
      (canonicalBackground (slot phase (sites R n)) (pairCoordinates.symm h) qt.2)))
    p (hG phase).1 (mul_pos hB (mesh_pos n)) hC hP hS (T.root hplane)
    (geometry_root hplane T R phase n) (geometry_anchor hplane T R phase n)
    hPb hp hpstop hgrowth hprofileCal hk hcutρ o
    (fun _ => insertion rule) (fun _ => insertion_centered rule) (fun _ => insertion_variation rule)
  rw [selected_ordered_full (slot phase (sites R n)) (testSupport hplane T n)
    (fun v hv => slot_covers phase (sites R n) v (hsupport n hv)) rule o
    (fun ξ => outer (fun qt => T.test n qt.1 (ξ qt.2)))
    (fun ω η hag => congrArg outer (test_local hplane T n hnlevel ω η hag))] at hh
  simpa only [abs_div,abs_of_pos (pow_pos hS k),ρ,Function.Embedding.refl_apply] using hh

#print axioms eventual_ordered_bound
end
end ExceptionalTimes.DyadicNormalizedForest
