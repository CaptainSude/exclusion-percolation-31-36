import ExceptionalTimes.ForestDegreeMass
import ExceptionalTimes.CircularStaticProfile
import ExceptionalTimes.LocalClockControl

/-! Uniform normalized all-degree mass for the actual clipped ordinary
arm profile and the actual local dimer clocks. The only probability inputs
are named ordinary static arm and attachment results. -/

open Filter
open scoped Classical BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.CircularForestMass
open PairSquareSewing CircularStaticProfile ForestGeometryEnvelope ForestDegreeMass
open ForestSelectionIntegral CanonicalForestOrdered ForestCoefficientIntegral
open SelectedPerturbation IndependentAnnulusInput LocalDimerCalibration LatticeRadial
open Source06Specialization LocalClockControl

variable {Bs : ℕ→Type*} [∀n,Fintype (Bs n)] {J : Type*} [Fintype J]

theorem eventual_profile_mass
    (s : ℕ→Finset Site) (anchor : ∀n,Bs n ↪ s n)
    (G : ∀n,(S : Finset (Bs n)) → DimerGeometry S J)
    {B C₄ Q c g stop r K : ℝ}
    (hstatic : PublishedCircularArmInputs B C₄ Q c g)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (hstop : 0<stop) (hstop1 : 4*stop<1) (hr : 0<r)
    (center : ℂ) (root : ℕ→J→ℂ)
    (hroot : ∀n S,(G n S).root=root n)
    (hanchor : ∀n (S : Finset (Bs n)) (i : S),
      position (G n S).mesh ((G n S).endpoint (i,0))=scaledEmbedding (mesh n) (anchor n i.val))
    (hmargin : ∀n S,(G n S).margin≤mesh n)
    (hs : ∀n v,v∈s n → ‖scaledEmbedding (mesh n) v-center‖≤r) :
    ∃A : ℝ,0≤A ∧ ∀ᶠ n in atTop,∀rule : Rule,∀k : ℕ,
      ((mesh n)^2/localS rule n)^k*
        geometryDegree (envelope (G n) (B*mesh n) stop (11*B*r) (max 1 (Q/c)) K g
          (profile (mesh n) (mesh_pos n) B stop)) k≤
        A^k*(k:ℝ)^(-(1-g/2)*k) := by
  have hB : 0<B := by linarith [hstatic.1]
  have hc : 0<c := hstatic.2.2.2.1
  have hg : 0<g := hstatic.2.2.2.2.1
  have hg2 : g<2 := hstatic.2.2.2.2.2.1
  obtain ⟨ca,hca,e0,he0,hloc⟩ := localS_lower B hattach
  let C := max 1 (Q/c)
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  let P := ((K*C^2*256^g)^2*Real.exp (g*(1+4/100)))*(C*stop^g)
  have hP : 0≤P := mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (mul_nonneg hC (Real.rpow_nonneg hstop.le _))
  let L := cutoffConstant B Q c g B stop/ca
  have hcutconst : 0≤cutoffConstant B Q c g B stop := by
    unfold cutoffConstant
    exact div_nonneg (mul_nonneg (div_nonneg (by linarith [hstatic.2.2.1]) hc.le)
      (Real.rpow_nonneg (div_nonneg hB.le hB.le) _)) (mul_nonneg hc.le (Real.rpow_nonneg hstop.le _))
  have hL : 0≤L := div_nonneg hcutconst hca.le
  let M := summationConstant (Fintype.card J) (min stop (11*B*r)) (11*B*r) C B g r
  have hM : 0≤M := summationConstant_nonneg _ (le_min hstop.le (by positivity))
  refine ⟨P*L*M,mul_nonneg (mul_nonneg hP hL) hM,?_⟩
  have hsmall : 0<min e0 (min r (stop/B)) := lt_min he0 (lt_min hr (div_pos hstop hB))
  filter_upwards [UnitClockControl.mesh_tendsto_zero.eventually (gt_mem_nhds hsmall)] with n hn
  have he0n : mesh n<e0 := hn.trans_le (min_le_left _ _)
  have her : mesh n≤r := (hn.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hecut : B*mesh n≤stop := by
    have h := hn.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (lt_div_iff₀ hB).mp h
    nlinarith
  have haSmall : 4*(B*mesh n)<1 := lt_of_le_of_lt (by linarith : 4*(B*mesh n)≤4*stop) hstop1
  have hprof := profile_pos hstatic (mesh n) (mesh_pos n) stop hecut hstop1
  have hprofstop := profile_at_stop hstatic (mesh n) (mesh_pos n) stop hecut hstop1
  have hgrowth := profile_growth hstatic (mesh n) (mesh_pos n) stop hecut hstop1
  have hcal := profile_cutoff_le_sourceArmCost hstatic (mesh n) (mesh_pos n) stop B
    le_rfl hecut hstop1 hB haSmall
  have harm : 0<sourceArmCost (mesh n) (B*mesh n) (mesh_pos n)
      (mul_pos hB (mesh_pos n)) haSmall := by
    rw [←cost_eq (mesh n) (mesh_pos n) (B*mesh n) (mul_pos hB (mesh_pos n)) haSmall]
    exact input_cost_pos hstatic (mesh n) (mesh_pos n) (B*mesh n) le_rfl
      (mul_pos hB (mesh_pos n)) haSmall
  intro rule k
  have hlocal := hloc n he0n hB haSmall rule
  have hS : 0<localS rule n := (mul_pos hca harm).trans_le hlocal
  have hprofileCal : profile (mesh n) (mesh_pos n) B stop (B*mesh n)≤L*localS rule n := by
    apply hcal.trans
    have hh := mul_le_mul_of_nonneg_left hlocal (div_nonneg hcutconst hca.le)
    have heq (a : ℝ) : (cutoffConstant B Q c g B stop/ca)*(ca*a)=
        cutoffConstant B Q c g B stop*a := by field_simp [hca.ne']
    rw [heq] at hh
    exact hh
  have hPb (S : Finset (Bs n)) : prefactor (G n S) (B*mesh n) stop C K g≤P := by
    apply prefactor_le (G n S) (mul_pos hB (mesh_pos n)) hstop.le hC hg.le
    have hB100 : (100:ℝ)≤B := by linarith [hstatic.1]
    have hmul := mul_le_mul_of_nonneg_right hB100 (mesh_pos n).le
    linarith [hmargin n S]
  exact all_degree_bound (s n) (anchor n) (G n) center (mesh_pos n) hB hg.le hg2 hecut her hC
    hP hL hS (hs n) (root n) (hroot n) (hanchor n) hPb
    (profile (mesh n) (mesh_pos n) B stop) hprof hprofstop hgrowth hprofileCal k

#print axioms eventual_profile_mass
end ExceptionalTimes.CircularForestMass

