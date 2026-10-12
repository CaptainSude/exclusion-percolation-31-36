import ExceptionalTimes.LocalDimerCalibration
import ExceptionalTimes.UnitClockControl

/-! The local reference clock itself has the required three-quarter
power growth. The finite central gadget supplies both update rules; all
remaining probability inputs are explicit ordinary static arm facts. -/

open Filter
open scoped Classical Topology
namespace ExceptionalTimes.LocalClockControl
noncomputable section
open PairSquareSewing UnitStaticAttachment Source06Specialization
open IndependentAnnulusInput LocalDimerCalibration UnitClockControl

theorem localS_lower (B0 : ℝ) (hattach : PublishedUnitAttachment B0) :
    ∃ c : ℝ,0<c ∧ ∃ e0 : ℝ,0<e0 ∧ ∀ n : ℕ,mesh n<e0 →
      ∀ hB : 0<B0,∀ hsmall : 4*(B0*mesh n)<1,∀ rule : Rule,
        c*sourceArmCost (mesh n) (B0*mesh n) (mesh_pos n)
          (mul_pos hB (mesh_pos n)) hsmall≤localS rule n := by
  obtain ⟨c,hc,e0,he0,hbound⟩ := published_local_response_any_cover B0 hattach
  refine ⟨c,hc,e0,he0,?_⟩
  intro n hn hB hs rule
  have hzero : Bulk (mesh n) (0 : Site) := by
    norm_num [Bulk,position,triangularEmbedding]
  exact hbound (mesh n) (mesh_pos n) hn hs 0 hzero rule (reference n).support
    (Finset.Subset.refl _)

theorem local_clock_control (B0 : ℝ) (hattach : PublishedUnitAttachment B0)
    (hpositive : PublishedCircularArmLower B0)
    (hexponent : PublishedDyadicFourArmLower B0) (rule : Rule) :
    AnnulusTransferMixing.NewClockControl (localClock rule) := by
  have hB : 0<B0 := by linarith [hattach.1]
  obtain ⟨c,hc,e0,he0,hlocal⟩ := localS_lower B0 hattach
  let cg : ℝ := c/2
  have hcg : 0<cg := by dsimp [cg]; positivity
  have hcut : 0<min e0 (1/(4*B0)) := lt_min he0 (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (mesh_tendsto_zero.eventually (gt_mem_nhds hcut))
  have hsmall (n : ℕ) (hn : N≤n) : 4*(B0*mesh n)<1 := by
    have ht := (hN n hn).trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0<4*B0 by positivity)).mp ht
    nlinarith
  have hS (n : ℕ) (hn : N≤n) :
      c*sourceArmCost (mesh n) (B0*mesh n) (mesh_pos n)
        (mul_pos hB (mesh_pos n)) (hsmall n hn) ≤ localS rule n :=
    hlocal n ((hN n hn).trans_le (min_le_left _ _)) hB (hsmall n hn) rule
  have hlower (n : ℕ) (hn : N≤n) :
      cg*((2^n:ℕ):ℝ)^2*sourceArmCost (mesh n) (B0*mesh n) (mesh_pos n)
        (mul_pos hB (mesh_pos n)) (hsmall n hn) ≤ localClock rule n := by
    have h := div_le_div_of_nonneg_right (hS n hn)
      (show 0≤2*(mesh n)^2 by positivity)
    change _≤localS rule n/(2*(mesh n)^2)
    convert h using 1
    dsimp only [cg,mesh]
    rw [Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  have hJ (n : ℕ) (hn : N≤n) : 0<localClock rule n := by
    have ha := sourceArmCost_pos_of_lower hpositive (mesh n) (mesh_pos n)
      (B0*mesh n) (mul_pos hB (mesh_pos n)) (hsmall n hn) le_rfl
    exact (mul_pos (mul_pos hcg (by positivity)) ha).trans_le (hlower n hn)
  apply absorb_finite_prefix (localClock rule) N hJ
  intro η hη0 _hη1
  obtain ⟨ca,hca,M,harm⟩ := hexponent.2 η hη0
  refine ⟨1/(2*(cg*ca)),by positivity,M,?_⟩
  intro n hn hm
  let q : ℝ := ((2^n:ℕ):ℝ)
  have hq : 0<q := by dsimp [q]; positivity
  have har := harm n hm hB (hsmall n hn)
  have hg := hlower n hn
  have hmul : q^2*q^(-(5/4+η))=q^(3/4-η) := by
    calc
      _=q^(2:ℝ)*q^(-(5/4+η)) := by rw [Real.rpow_two]
      _=q^((2:ℝ)+(-(5/4+η))) := (Real.rpow_add hq _ _).symm
      _=_ := by congr 1; ring
  have hmain : (cg*ca)*q^(3/4-η)≤localClock rule n := by
    have hh := mul_le_mul_of_nonneg_left har (show 0≤cg*q^2 by positivity)
    calc
      _=(cg*q^2)*(ca*q^(-(5/4+η))) := by rw [←hmul]; ring
      _≤_ := hh.trans hg
  have hden : 0<2*(cg*ca)*q^(3/4-η) := by positivity
  have hdiv := one_div_le_one_div_of_le hden
    (show 2*(cg*ca)*q^(3/4-η)≤2*localClock rule n by linarith)
  calc
    _≤1/(2*(cg*ca)*q^(3/4-η)) := hdiv
    _=(1/(2*(cg*ca)))*q^(-(3/4-η)) := by
      rw [Real.rpow_neg hq.le]
      ring

#print axioms local_clock_control
end
end ExceptionalTimes.LocalClockControl
