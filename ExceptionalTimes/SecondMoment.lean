import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! A nonnegative second-moment estimate with extended-real mass and energy.
No boundedness or finiteness of the random variable is silently presumed. -/

namespace ExceptionalTimes.SecondMoment

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem lintegral_sq_le (μ : Measure Ω) {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω, f ω ∂μ) ^ 2 ≤ (∫⁻ ω, f ω ^ 2 ∂μ) * μ univ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable (f := f) (g := fun _ => 1) measurable_const.aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.rpow_two, one_pow, lintegral_const, one_mul] at h
  have hs (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    _ ≤ ((∫⁻ ω, f ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ univ) ^ (1 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left' h 2
    _ = _ := by rw [mul_pow, hs, hs]

/-- Paley--Zygmund at threshold one half, with mean normalized to one. -/
theorem quarter_le_secondMoment_mul_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) (hmean : ∫⁻ ω, f ω ∂μ = 1)
    {B : ℝ≥0∞} (hsecond : (∫⁻ ω, f ω ^ 2 ∂μ) ≤ B) :
    (1 / 4 : ℝ≥0∞) ≤ B * μ {ω | (1 / 2 : ℝ≥0∞) < f ω} := by
  let A : Set Ω := {ω | (1 / 2 : ℝ≥0∞) < f ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  have hlow : (∫⁻ ω in Aᶜ, f ω ∂μ) ≤ 1 / 2 := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1 / 2 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' hA.compl
        intro ω hω
        exact le_of_not_gt hω
      _ = (1 / 2 : ℝ≥0∞) * μ Aᶜ := by simp
      _ ≤ (1 / 2 : ℝ≥0∞) * 1 := mul_le_mul' le_rfl (prob_le_one)
      _ = _ := mul_one _
  have hhalf : (1 / 2 : ℝ≥0∞) ≤ ∫⁻ ω in A, f ω ∂μ := by
    have hsplit := lintegral_add_compl (μ := μ) f hA
    rw [hmean] at hsplit
    have hsum : (1 : ℝ≥0∞) ≤ (∫⁻ ω in A, f ω ∂μ) + 1 / 2 := by
      exact hsplit.symm.trans_le (add_le_add le_rfl hlow)
    have hh := (tsub_le_iff_right.mpr hsum)
    norm_num at hh
    simpa only [one_div] using hh
  calc
    (1 / 4 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) ^ 2 := by
      norm_num only [one_div]
      rw [← ENNReal.inv_pow]
      norm_num
    _ ≤ (∫⁻ ω in A, f ω ∂μ) ^ 2 := pow_le_pow_left' hhalf 2
    _ ≤ (∫⁻ ω in A, f ω ^ 2 ∂μ) * (μ.restrict A) univ :=
      lintegral_sq_le (μ.restrict A) hf
    _ ≤ B * μ A := by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact mul_le_mul' ((setLIntegral_le_lintegral A _).trans hsecond) le_rfl

theorem secondMoment_probability_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) (hmean : ∫⁻ ω, f ω ∂μ = 1)
    {B : ℝ≥0∞} (hB : B ≠ 0) (hBt : B ≠ ⊤)
    (hsecond : (∫⁻ ω, f ω ^ 2 ∂μ) ≤ B) :
    (1 / 4 : ℝ≥0∞) / B ≤ μ {ω | (1 / 2 : ℝ≥0∞) < f ω} := by
  apply (ENNReal.div_le_iff' hB hBt).mpr
  exact quarter_le_secondMoment_mul_probability μ hf hmean hsecond

/-- Intersect the mass witness with a bounded-energy event. This is the
literal second-moment/Markov combination; no independence is needed. -/
theorem mass_energy_probability_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hmean : ∫⁻ ω, f ω ∂μ = 1)
    {B D T : ℝ≥0∞} (hB : B ≠ 0) (hBt : B ≠ ⊤) (hT : T ≠ 0) (hTt : T ≠ ⊤)
    (hsecond : (∫⁻ ω, f ω ^ 2 ∂μ) ≤ B) (henergy : (∫⁻ ω, g ω ∂μ) ≤ D) :
    (1 / 4 : ℝ≥0∞) / B - D / T ≤
      μ {ω | (1 / 2 : ℝ≥0∞) < f ω ∧ g ω ≤ T} := by
  have hm := secondMoment_probability_lower μ hf hmean hB hBt hsecond
  have hgT : μ {ω | T < g ω} ≤ D / T := by
    calc
      _ ≤ μ {ω | T ≤ g ω} := measure_mono (fun ω (h : T < g ω) => show T ≤ g ω from h.le)
      _ ≤ (∫⁻ ω, g ω ∂μ) / T := meas_ge_le_lintegral_div hg.aemeasurable hT hTt
      _ ≤ D / T := ENNReal.div_le_div_right henergy T
  calc
    _ ≤ μ {ω | (1 / 2 : ℝ≥0∞) < f ω} - μ {ω | T < g ω} :=
      tsub_le_tsub hm hgT
    _ ≤ μ ({ω | (1 / 2 : ℝ≥0∞) < f ω} \ {ω | T < g ω}) := le_measure_sdiff
    _ = _ := by congr 1; ext ω; simp

/-- A single explicit finite constant works in the capacity criterion:
`C = 8 B² + 2`. Both the second moment and the expected energy may be bounded
by `B`; success then has probability at least `1/(8B)`. -/
theorem capacity_witness_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hmean : ∫⁻ ω, f ω ∂μ = 1) {B : ℝ} (hB : 0 < B)
    (hsecond : (∫⁻ ω, f ω ^ 2 ∂μ) ≤ ENNReal.ofReal B)
    (henergy : (∫⁻ ω, g ω ∂μ) ≤ ENNReal.ofReal B) :
    ENNReal.ofReal (1 / (8 * B)) ≤
      μ {ω | ENNReal.ofReal (1 / (8 * B ^ 2 + 2)) < f ω ∧
        g ω ≤ ENNReal.ofReal (8 * B ^ 2 + 2)} := by
  let C : ℝ := 8 * B ^ 2 + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall : (1 : ℝ) / C ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hC (by norm_num : (0 : ℝ) < 2)).mpr
    dsimp [C]
    nlinarith [sq_nonneg B]
  have hratio : B / C ≤ 1 / (8 * B) := by
    apply (div_le_div_iff₀ hC (by positivity : 0 < 8 * B)).mpr
    dsimp [C]
    nlinarith
  have hid : (1 / 4 : ℝ) / B = 1 / (8 * B) + 1 / (8 * B) := by
    field_simp
    ring
  have hn : 1 / (8 * B) ≤ (1 / 4 : ℝ) / B - B / C := by rw [hid]; linarith
  have heq : (1 / 4 : ℝ≥0∞) / ENNReal.ofReal B - ENNReal.ofReal B / ENNReal.ofReal C =
      ENNReal.ofReal ((1 / 4 : ℝ) / B - B / C) := by
    rw [ENNReal.ofReal_sub _ (div_nonneg hB.le hC.le),
      ENNReal.ofReal_div_of_pos hB, ENNReal.ofReal_div_of_pos hC]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hp := mass_energy_probability_lower μ hf hg hmean
    (B := ENNReal.ofReal B) (D := ENNReal.ofReal B) (T := ENNReal.ofReal C)
    (by positivity) ENNReal.ofReal_ne_top (by positivity) ENNReal.ofReal_ne_top hsecond henergy
  rw [heq] at hp
  apply (ENNReal.ofReal_le_ofReal hn).trans (hp.trans (measure_mono _))
  intro ω hω
  refine ⟨lt_of_le_of_lt ?_ hω.1, hω.2⟩
  simpa using ENNReal.ofReal_le_ofReal hsmall

end ExceptionalTimes.SecondMoment

#print axioms ExceptionalTimes.SecondMoment.secondMoment_probability_lower
#print axioms ExceptionalTimes.SecondMoment.capacity_witness_probability
