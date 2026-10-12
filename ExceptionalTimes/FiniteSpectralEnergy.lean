import ExceptionalTimes.FiniteFractional
import ExceptionalTimes.FrostmanEnergy
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Spectral time energy of actual finite matrices

This module derives the damped time-energy identity from mathlib's matrix
spectral theorem and scalar Gamma integral. The time evolution here is the
literal matrix exponential. Identifying it with independent Poisson swaps
is a separate finite continuous-time Markov-chain construction theorem.
-/

open MeasureTheory Set
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace ExceptionalTimes.FiniteSpectralEnergy

open ExceptionalTimes.FiniteFractional

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def spectralWeight {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) (i : Ω) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ *
    Complex.normSq (((star (hA.eigenvectorUnitary : Matrix Ω Ω ℂ)) *ᵥ f) i)

theorem spectralWeight_nonneg {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) (i : Ω) : 0 ≤ spectralWeight hA f i := by
  unfold spectralWeight
  exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)

theorem quadraticForm_conjugate_diagonal (U : Matrix Ω Ω ℂ)
    (d : Ω → ℝ) (f : Ω → ℂ) :
    uniformQuadraticForm (U * Matrix.diagonal (fun i => (d i : ℂ)) * star U) f =
      (Fintype.card Ω : ℝ)⁻¹ *
        ∑ i, d i * Complex.normSq ((star U *ᵥ f) i) := by
  unfold uniformQuadraticForm
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hv : star f ᵥ* U = star (star U *ᵥ f) := by
    rw [Matrix.star_mulVec]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [hv]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.normSq_apply]
  ring

theorem uniformQuadraticForm_cfc {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (φ : ℝ → ℝ) (f : Ω → ℂ) :
    uniformQuadraticForm (cfc φ A) f =
      ∑ i, spectralWeight hA f i * φ (hA.eigenvalues i) := by
  rw [hA.cfc_eq]
  change uniformQuadraticForm
    ((hA.eigenvectorUnitary : Matrix Ω Ω ℂ) *
      Matrix.diagonal (fun i => (φ (hA.eigenvalues i) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix Ω Ω ℂ)) f = _
  rw [quadraticForm_conjugate_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold spectralWeight
  ring

theorem exp_neg_smul_eq_cfc {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((-t) • A) = cfc (fun x : ℝ => Real.exp (-(t * x))) A := by
  rw [← CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all (-t)).smul hA.isSelfAdjoint)]
  simpa only [smul_eq_mul, neg_mul] using
    (cfc_comp_smul (-t) Real.exp A (ha := hA.isSelfAdjoint)).symm

theorem fractional_inverse_eq_cfc {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef) (s : ℝ) :
    CFC.rpow (Ring.inverse (1 + A)) s =
      cfc (fun x : ℝ => (1 + x) ^ (-s)) A := by
  have hp : IsStrictlyPositive (1 + A) := isStrictlyPositive_one.add_nonneg hA.nonneg
  change (Ring.inverse (1 + A)) ^ s = _
  rw [CFC.inverse_eq_rpow_neg_one hp, CFC.rpow_rpow _ _ _ (by norm_num) hp]
  simp only [neg_one_mul]
  have hplus : cfc (fun x : ℝ => 1 + x) A = 1 + A := by
    rw [cfc_const_add (1 : ℝ) (fun x : ℝ => x) A (ha := hA.isHermitian.isSelfAdjoint)]
    rw [map_one]
    congr 1
    exact cfc_id' ℝ A hA.isHermitian.isSelfAdjoint
  rw [← hplus]
  apply CFC.cfc_rpow (hf₂ := by fun_prop) (ha := hA.isHermitian.isSelfAdjoint)
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
  linarith

/-- Actual matrix-exponential autocorrelation in the uniform inner product. -/
noncomputable def correlation (A : Matrix Ω Ω ℂ) (f : Ω → ℂ) (t : ℝ) : ℝ :=
  uniformQuadraticForm (NormedSpace.exp ((-t) • A)) f

theorem correlation_spectral {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) (t : ℝ) :
    correlation A f t = ∑ i, spectralWeight hA f i * Real.exp (-(t * hA.eigenvalues i)) := by
  unfold correlation
  rw [exp_neg_smul_eq_cfc hA, uniformQuadraticForm_cfc hA]

theorem scalar_laplace {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) :
    ∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ (s - 1) * Real.exp (-(t * ℓ)) =
      Real.Gamma s * (1 + ℓ) ^ (-s) := by
  have hfun : (fun t : ℝ => Real.exp (-t) * t ^ (s - 1) * Real.exp (-(t * ℓ))) =
      (fun t : ℝ => t ^ (s - 1) * Real.exp (-((1 + ℓ) * t))) := by
    funext t
    rw [mul_comm (Real.exp (-t)), mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfun, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by linarith)]
  rw [one_div, Real.inv_rpow (by linarith : 0 ≤ 1 + ℓ), Real.rpow_neg (by linarith)]
  ring

theorem scalar_laplace_integrable {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 ≤ ℓ) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-t) * t ^ (s - 1) * Real.exp (-(t * ℓ))) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := s - 1) (p := 1) (b := 1 + ℓ) (by linarith) (by norm_num) (by linarith)
  convert hi using 1
  funext t
  rw [Real.rpow_one, mul_comm (Real.exp (-t)), mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Exponential damping makes zero spectral modes integrable for every s>0. -/
noncomputable def weightedEnergy (A : Matrix Ω Ω ℂ) (f : Ω → ℂ) (s : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ (s - 1) * correlation A f t

theorem weighted_integrand_spectral {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) (s t : ℝ) :
    Real.exp (-t) * t ^ (s - 1) * correlation A f t =
      ∑ i, spectralWeight hA f i *
        (Real.exp (-t) * t ^ (s - 1) * Real.exp (-(t * hA.eigenvalues i))) := by
  rw [correlation_spectral hA, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weighted_integrable {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (s - 1) * correlation A f t) (Ioi 0) := by
  simp_rw [weighted_integrand_spectral hA.isHermitian]
  apply integrable_finsetSum
  intro i _
  exact (scalar_laplace_integrable hs (hA.eigenvalues_nonneg i)).const_mul _

/-- The weighted time integral of the literal matrix exponential is the
Gamma factor times the same fractional quadratic form used in comparison. -/
theorem weightedEnergy_eq_fractional {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs : 0 < s) :
    weightedEnergy A f s = Real.Gamma s *
      uniformQuadraticForm (CFC.rpow (Ring.inverse (1 + A)) s) f := by
  unfold weightedEnergy
  simp_rw [weighted_integrand_spectral hA.isHermitian]
  rw [integral_finsetSum _ (fun i _ =>
    (scalar_laplace_integrable hs (hA.eigenvalues_nonneg i)).const_mul _)]
  simp_rw [integral_const_mul, scalar_laplace hs (hA.eigenvalues_nonneg _)]
  rw [fractional_inverse_eq_cfc hA, uniformQuadraticForm_cfc hA.isHermitian, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Finite-dimensional energy comparison, directly about actual matrix
exponentials and with the Gamma normalization fully derived. -/
theorem weightedEnergy_mono {A B : Matrix Ω Ω ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    (f : Ω → ℂ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    weightedEnergy B f s ≤ weightedEnergy A f s := by
  rw [weightedEnergy_eq_fractional hA f hs0, weightedEnergy_eq_fractional hB f hs0]
  apply mul_le_mul_of_nonneg_left _ (Real.Gamma_pos_of_pos hs0).le
  apply uniformQuadraticForm_mono
  exact ExceptionalTimesPilot.shifted_fractional_inverse_order ⟨hs0.le, hs1⟩
    isStrictlyPositive_one hA.nonneg hAB

theorem correlation_nonneg {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) (t : ℝ) : 0 ≤ correlation A f t := by
  rw [correlation_spectral hA]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (spectralWeight_nonneg hA f i) (Real.exp_pos _).le

theorem correlation_antitone {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) : Antitone (correlation A f) := by
  intro t u htu
  simp_rw [correlation_spectral hA.isHermitian]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (spectralWeight_nonneg _ _ _)
  exact Real.exp_le_exp.mpr (neg_le_neg
    (mul_le_mul_of_nonneg_right htu (hA.eigenvalues_nonneg i)))

theorem measurable_correlation {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) : Measurable (correlation A f) := by
  simp_rw [show correlation A f = fun t =>
    ∑ i, spectralWeight hA f i * Real.exp (-(t * hA.eigenvalues i)) from
      funext (correlation_spectral hA f)]
  fun_prop

theorem short_integrand_nonneg {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t ^ (s - 1) * correlation A f t :=
  mul_nonneg (Real.rpow_nonneg ht _) (correlation_nonneg hA f t)

theorem short_integrand_le_damped {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    (f : Ω → ℂ) (s : ℝ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    t ^ (s - 1) * correlation A f t ≤
      Real.exp 1 * (Real.exp (-t) * t ^ (s - 1) * correlation A f t) := by
  have he : 1 ≤ Real.exp 1 * Real.exp (-t) := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith [ht.2]
  have hp := short_integrand_nonneg hA f s ht.1.le
  nlinarith

/-- The undamped energy on the unit time window. Endpoints have zero
Lebesgue measure, so Ioc has the same integral as Ioo. -/
noncomputable def shortEnergy (A : Matrix Ω Ω ℂ) (f : Ω → ℂ) (s : ℝ) : ℝ :=
  ∫ t : ℝ in Ioc 0 1, t ^ (s - 1) * correlation A f t

theorem short_integrable {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * correlation A f t) (Ioc 0 1) := by
  have hm : Measurable (fun t : ℝ => t ^ (s - 1) * correlation A f t) :=
    (measurable_id.pow_const _).mul (measurable_correlation hA.isHermitian f)
  apply (((weighted_integrable hA f hs).mono_set Ioc_subset_Ioi_self).const_mul
    (Real.exp 1)).mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (short_integrand_nonneg hA.isHermitian f s ht.1.le)]
  exact short_integrand_le_damped hA.isHermitian f s ht

theorem shortEnergy_le_weighted {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs : 0 < s) :
    shortEnergy A f s ≤ Real.exp 1 * weightedEnergy A f s := by
  have hi := weighted_integrable hA f hs
  have hsmall := setIntegral_mono_on (short_integrable hA f hs)
    ((hi.mono_set Ioc_subset_Ioi_self).const_mul (Real.exp 1))
    measurableSet_Ioc (fun t ht => short_integrand_le_damped hA.isHermitian f s ht)
  rw [integral_const_mul] at hsmall
  apply hsmall.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
  apply setIntegral_mono_set hi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le
      (short_integrand_nonneg hA.isHermitian f s ht.le) |>.trans_eq (by ring)
  · exact Filter.Eventually.of_forall fun _ ht => ht.1

theorem correlation_one_le_shortEnergy {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    correlation A f 1 ≤ shortEnergy A f s := by
  have hc : IntegrableOn (fun _ : ℝ => correlation A f 1) (Ioc (0 : ℝ) 1) :=
    integrableOn_const (by simp)
  have hi := setIntegral_mono_on hc (short_integrable hA f hs0) measurableSet_Ioc
    (fun t ht => show correlation A f 1 ≤ t ^ (s - 1) * correlation A f t from by
      have hq := correlation_antitone hA f ht.2
      have hn := correlation_nonneg hA.isHermitian f t
      have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (sub_nonpos.mpr hs1)
      nlinarith)
  simpa [shortEnergy] using hi

theorem damped_initial_le_shortEnergy {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ in Ioc 0 1, Real.exp (-t) * t ^ (s - 1) * correlation A f t) ≤
      shortEnergy A f s := by
  apply setIntegral_mono_on ((weighted_integrable hA f hs).mono_set Ioc_subset_Ioi_self)
    (short_integrable hA f hs) measurableSet_Ioc
  intro t ht
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
  have hp := short_integrand_nonneg hA.isHermitian f s ht.1.le
  nlinarith

theorem damped_tail_le_correlation_one {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (∫ t : ℝ in Ioi 1, Real.exp (-t) * t ^ (s - 1) * correlation A f t) ≤
      Real.exp (-1) * correlation A f 1 := by
  have ht : IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ (s - 1) * correlation A f t) (Ioi 1) :=
    (weighted_integrable hA f hs0).mono_set (Ioi_subset_Ioi (by norm_num))
  have hc := (integrableOn_exp_neg_Ioi 1).mul_const (correlation A f 1)
  have hi := setIntegral_mono_on ht hc measurableSet_Ioi
    (fun t ht => show Real.exp (-t) * t ^ (s - 1) * correlation A f t ≤
        Real.exp (-t) * correlation A f 1 from by
      have hp := Real.rpow_le_one_of_one_le_of_nonpos ht.le (sub_nonpos.mpr hs1)
      have hq := correlation_antitone hA f ht.le
      have hn := correlation_nonneg hA.isHermitian f t
      have hmul : t ^ (s - 1) * correlation A f t ≤ correlation A f 1 := by
        nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul (Real.exp_pos (-t)).le)
  simpa only [integral_mul_const, integral_exp_neg_Ioi] using hi

theorem weightedEnergy_le_short {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    weightedEnergy A f s ≤ (1 + Real.exp (-1)) * shortEnergy A f s := by
  have hi := weighted_integrable hA f hs0
  have hd : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr (fun _ hx hy => not_lt_of_ge hx.2 hy)
  have hsplit : weightedEnergy A f s =
      (∫ t : ℝ in Ioc 0 1, Real.exp (-t) * t ^ (s - 1) * correlation A f t) +
      (∫ t : ℝ in Ioi 1, Real.exp (-t) * t ^ (s - 1) * correlation A f t) := by
    unfold weightedEnergy
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_union hd measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi (by norm_num)))
  rw [hsplit]
  have hfirst := damped_initial_le_shortEnergy hA f hs0
  have htail := damped_tail_le_correlation_one hA f hs0 hs1
  have hlast := mul_le_mul_of_nonneg_left (correlation_one_le_shortEnergy hA f hs0 hs1)
    (Real.exp_pos (-1)).le
  linarith

/-- Actual finite matrix exponential energies transfer on (0,1) with
the explicit universal constant e+1. No pointwise semigroup order is used. -/
theorem shortEnergy_comparison {A B : Matrix Ω Ω ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    (f : Ω → ℂ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    shortEnergy B f s ≤ (Real.exp 1 + 1) * shortEnergy A f s := by
  calc
    shortEnergy B f s ≤ Real.exp 1 * weightedEnergy B f s :=
      shortEnergy_le_weighted hB f hs0
    _ ≤ Real.exp 1 * weightedEnergy A f s :=
      mul_le_mul_of_nonneg_left (weightedEnergy_mono hA hB hAB f hs0 hs1) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * ((1 + Real.exp (-1)) * shortEnergy A f s) :=
      mul_le_mul_of_nonneg_left (weightedEnergy_le_short hA f hs0 hs1) (Real.exp_pos 1).le
    _ = _ := by
      have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
      calc
        _ = (Real.exp 1 + Real.exp 1 * Real.exp (-1)) * shortEnergy A f s := by ring
        _ = _ := by rw [he]

/-- This is exactly the extended nonnegative energy used by the clock
truncation/Fatou argument. The diagonal is excluded by Ioc; it is never
assigned an artificially finite Frostman-kernel value. -/
theorem frostman_lintegral_eq_shortEnergy {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef)
    (f : Ω → ℂ) {γ : ℝ} (hγ : γ < 1) :
    (∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t * ENNReal.ofReal (correlation A f t)) =
      ENNReal.ofReal (shortEnergy A f (1 - γ)) := by
  unfold shortEnergy
  rw [ofReal_integral_eq_lintegral_ofReal (short_integrable hA f (by linarith))
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact short_integrand_nonneg hA.isHermitian f (1 - γ) ht.1.le)]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  rw [frostmanKernel_off_diagonal γ (ne_of_lt ht.1)]
  have hd : dist (0 : ℝ) t = t := by simp [Real.dist_eq, abs_of_pos ht.1]
  rw [hd, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _)]
  congr 1
  congr 1
  ring

theorem frostman_lintegral_comparison {A B : Matrix Ω Ω ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    (f : Ω → ℂ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t * ENNReal.ofReal (correlation B f t)) ≤
      ENNReal.ofReal (Real.exp 1 + 1) *
        ∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t * ENNReal.ofReal (correlation A f t) := by
  rw [frostman_lintegral_eq_shortEnergy hA f hγ1,
    frostman_lintegral_eq_shortEnergy hB f hγ1,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp 1 + 1)]
  exact ENNReal.ofReal_le_ofReal (shortEnergy_comparison hA hB hAB f (by linarith) (by linarith))

section SwapGenerators

open ExceptionalTimes.FiniteGenerator

variable {I : Type*} [Fintype I]

/-- Applied to the literal finite swap generator arrays. -/
theorem swap_generator_shortEnergy_comparison (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) {r₀ r₁ : I → ℝ}
    (hr₀ : ∀ i, 0 ≤ r₀ i) (hr : ∀ i, r₀ i ≤ r₁ i)
    (f : Ω → ℂ) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    shortEnergy (complexGenerator σ r₁) f s ≤
      (Real.exp 1 + 1) * shortEnergy (complexGenerator σ r₀) f s :=
  shortEnergy_comparison
    (Matrix.nonneg_iff_posSemidef.mp (complexGenerator_nonneg σ hσ r₀ hr₀))
    (Matrix.nonneg_iff_posSemidef.mp (complexGenerator_nonneg σ hσ r₁
      (fun i => (hr₀ i).trans (hr i))))
    (complexGenerator_mono σ hσ hr) f hs0 hs1

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unit-rate actual color exchanges versus rate-one canonical refresh of
selected pairs, whose swap rates are 1/2. Disjointness is needed to use
the independent dimer law, but not for this finite matrix comparison. -/
theorem colorSwap_half_rate_shortEnergy_comparison (edge : I → V × V)
    (selected : I → Bool) (f : (V → Bool) → ℂ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    shortEnergy
      (complexGenerator (fun i => colorSwap (edge i).1 (edge i).2) (fun _ => 1)) f s ≤
      (Real.exp 1 + 1) * shortEnergy
        (complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
          (fun i => if selected i then (1 / 2 : ℝ) else 0)) f s := by
  apply swap_generator_shortEnergy_comparison _ (fun _ => colorSwap_involutive _ _)
    _ _ f hs0 hs1
  · intro i
    split <;> norm_num
  · intro i
    split <;> norm_num

end SwapGenerators

#print axioms uniformQuadraticForm_cfc
#print axioms weightedEnergy_eq_fractional
#print axioms weightedEnergy_mono
#print axioms shortEnergy_comparison
#print axioms frostman_lintegral_comparison
#print axioms colorSwap_half_rate_shortEnergy_comparison

end ExceptionalTimes.FiniteSpectralEnergy
