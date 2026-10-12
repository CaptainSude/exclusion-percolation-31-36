import ExceptionalTimes.UnitJumpLower
import ExceptionalTimes.SourceCalibrationSampling
import ExceptionalTimes.AnnulusTransferMixing

/-! The concrete minimum of the two phase jump sums satisfies the clock
control required downstream. Static inputs only: the checked-gadget
attachment consequence, ordinary circular-arm positivity, and the static
5/4 exponent with any loss. The last input is a conventional consequence
of Smirnov--Werner math/0109120 (polychromatic alternating four arms) and
Nolin arm separation/quasi-multiplicativity, with source02 fixed-cut
comparison. Its deduction is outside Lean, not a verbatim source claim.
Finite-prefix absorption and all conversion to the swap clock are proved.
-/

open Filter
open scoped Classical BigOperators Topology
namespace ExceptionalTimes.UnitClockControl
noncomputable section
open PairSquareSewing UnitStaticAttachment UnitJumpLower IndependentAnnulusInput
open Source06Specialization

def minimumJump (n : ℕ) : ℝ := min (referenceJump false n) (referenceJump true n)

/-- Ordinary static dyadic four-arm exponent, with literal finite iid
circular-cut cost. The loss-dependent cutoff is explicit. -/
def PublishedDyadicFourArmLower (B0 : ℝ) : Prop :=
  128≤B0 ∧ ∀ η : ℝ,0<η → ∃ c : ℝ,0<c ∧ ∃ N : ℕ,
    ∀ n : ℕ,N≤n → ∀ hB : 0<B0,∀ hsmall : 4*(B0*mesh n)<1,
      c*((2^n:ℕ):ℝ)^(-(5/4+η)) ≤
        sourceArmCost (mesh n) (B0*mesh n) (mesh_pos n) (mul_pos hB (mesh_pos n)) hsmall

theorem mesh_tendsto_zero : Tendsto mesh atTop (𝓝 (0:ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤(2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹<1)
  change Tendsto (fun n : ℕ => ((2:ℝ)^n)⁻¹) atTop (𝓝 0)
  simpa only [inv_pow] using h

/-- An eventual power bound and positivity at one common threshold imply
the same power bound on its finite prefix, with a larger constant. -/
theorem absorb_finite_prefix (J : ℕ→ℝ) (N : ℕ)
    (hJ : ∀ n,N≤n → 0<J n)
    (hpow : ∀ η : ℝ,0<η → η<3/4 → ∃ C : ℝ,0≤C ∧ ∃ M : ℕ,
      ∀ n,N≤n → M≤n → 1/(2*J n)≤C*((2^n:ℕ):ℝ)^(-(3/4-η))) :
    AnnulusTransferMixing.NewClockControl J := by
  refine ⟨N,hJ,?_⟩
  intro η hη0 hη1
  obtain ⟨C,hC,M,hbound⟩ := hpow η hη0 hη1
  let w : ℕ→ℝ := fun n => ((2^n:ℕ):ℝ)^(-(3/4-η))
  have hw (n : ℕ) : 0<w n := Real.rpow_pos_of_pos (by positivity) _
  let P : ℝ := ∑ i∈Finset.range M,max 0 ((1/(2*J i))/w i)
  have hP : 0≤P := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨P+C,add_nonneg hP hC,?_⟩
  intro n hn
  by_cases hm : M≤n
  · exact (hbound n hn hm).trans (mul_le_mul_of_nonneg_right (by linarith) (hw n).le)
  · have hmem : n∈Finset.range M := Finset.mem_range.mpr (by omega)
    have hr : (1/(2*J n))/w n≤P := (le_max_right _ _).trans
      (Finset.single_le_sum (fun i _ => le_max_left 0 ((1/(2*J i))/w i)) hmem)
    exact ((div_le_iff₀ (hw n)).mp hr).trans
      (mul_le_mul_of_nonneg_right (by linarith) (hw n).le)

theorem minimumJump_clock_control (B0 : ℝ)
    (hattach : PublishedUnitAttachment B0)
    (hpositive : PublishedCircularArmLower B0)
    (hexponent : PublishedDyadicFourArmLower B0) :
    AnnulusTransferMixing.NewClockControl minimumJump := by
  have hB : 0<B0 := by linarith [hattach.1]
  obtain ⟨cg,hcg,e0,he0,hglobal⟩ := referenceJump_lower B0 hattach
  have hcut : 0<min e0 (1/(4*B0)) := lt_min he0 (by positivity)
  have hevent : ∀ᶠ n in atTop,6≤n ∧ mesh n<min e0 (1/(4*B0)) :=
    (eventually_ge_atTop 6).and (mesh_tendsto_zero.eventually (gt_mem_nhds hcut))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  have hsmall (n : ℕ) (hn : N≤n) : 4*(B0*mesh n)<1 := by
    have ht := (hN n hn).2.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (show 0<4*B0 by positivity)).mp ht
    nlinarith
  have hlower (n : ℕ) (hn : N≤n) :
      cg*((2^n:ℕ):ℝ)^2*sourceArmCost (mesh n) (B0*mesh n) (mesh_pos n)
        (mul_pos hB (mesh_pos n)) (hsmall n hn) ≤ minimumJump n := by
    have hphase (phase : Bool) :
        cg*((2^n:ℕ):ℝ)^2*sourceArmCost (mesh n) (B0*mesh n) (mesh_pos n)
          (mul_pos hB (mesh_pos n)) (hsmall n hn) ≤ referenceJump phase n := by
      have hh := hglobal phase n (hN n hn).1
        ((hN n hn).2.trans_le (min_le_left _ _)) (hsmall n hn)
      convert hh using 1
      simp only [Nat.cast_pow,Nat.cast_ofNat,pow_mul,mul_comm 2 n]
    exact le_min (hphase false) (hphase true)
  have hJ (n : ℕ) (hn : N≤n) : 0<minimumJump n := by
    have ha := sourceArmCost_pos_of_lower hpositive (mesh n) (mesh_pos n)
      (B0*mesh n) (mul_pos hB (mesh_pos n)) (hsmall n hn) le_rfl
    exact (mul_pos (mul_pos hcg (by positivity)) ha).trans_le (hlower n hn)
  apply absorb_finite_prefix minimumJump N hJ
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
  have hmain : (cg*ca)*q^(3/4-η)≤minimumJump n := by
    have hh := mul_le_mul_of_nonneg_left har (show 0≤cg*q^2 by positivity)
    calc
      _=(cg*q^2)*(ca*q^(-(5/4+η))) := by rw [←hmul]; ring
      _≤_ := hh.trans hg
  have hden : 0<2*(cg*ca)*q^(3/4-η) := by positivity
  have hdiv := one_div_le_one_div_of_le hden
    (show 2*(cg*ca)*q^(3/4-η)≤2*minimumJump n by linarith)
  calc
    _≤1/(2*(cg*ca)*q^(3/4-η)) := hdiv
    _=(1/(2*(cg*ca)))*q^(-(3/4-η)) := by
      rw [Real.rpow_neg hq.le]
      ring

#print axioms absorb_finite_prefix
#print axioms minimumJump_clock_control
end
end ExceptionalTimes.UnitClockControl
