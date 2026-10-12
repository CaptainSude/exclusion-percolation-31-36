import ExceptionalTimes.FiniteSpectralEnergy
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The Euler limit needed for the finite Poisson count-grid construction.
It is proved for the literal finite Hermitian matrices, without a CTMC input.
The stochastic count-grid approximation itself is a separate obligation. -/

namespace ExceptionalTimes.EulerSemigroup

open Filter FiniteSpectralEnergy
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem scalar_euler_limit {r : ℕ → ℝ} {t : ℝ}
    (hr : Tendsto (fun n : ℕ => n * r n) atTop (𝓝 t)) (x : ℝ) :
    Tendsto (fun n : ℕ => (1 - r n * x) ^ n) atTop (𝓝 (Real.exp (-(t * x)))) := by
  have h : Tendsto (fun n : ℕ => n * (-r n * x)) atTop (𝓝 (-(t * x))) := by
    convert hr.neg.mul_const x using 1 <;> simp only [neg_mul]
    funext n
    ring
  simpa only [neg_mul, ← sub_eq_add_neg] using Real.tendsto_one_add_pow_exp_of_tendsto h

theorem step_power_eq_cfc {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian) (r : ℝ) (n : ℕ) :
    (1 - r • A) ^ n = cfc (fun x : ℝ => (1 - r * x) ^ n) A := by
  rw [cfc_pow _ _ _ (ha := hA.isSelfAdjoint),
    cfc_sub _ _ A, cfc_const_mul_id _ _ hA.isSelfAdjoint]
  rw [cfc_const_one A (R := ℝ) hA.isSelfAdjoint]

/-- A perturbed Euler time step needs only n*r(n)→t. This includes the
Poisson-grid coefficient r(n)=(t/n)*exp(-Λ*t/n). -/
theorem matrix_euler_limit {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian)
    {r : ℕ → ℝ} {t : ℝ} (hr : Tendsto (fun n : ℕ => n * r n) atTop (𝓝 t)) :
    Tendsto (fun n : ℕ => (1 - r n • A) ^ n) atTop
      (𝓝 (NormedSpace.exp ((-t) • A))) := by
  let U : Matrix Ω Ω ℂ := hA.eigenvectorUnitary
  have hd : Tendsto
      (fun n : ℕ => Matrix.diagonal (fun i : Ω => (((1 - r n * hA.eigenvalues i) ^ n : ℝ) : ℂ)))
      atTop (𝓝 (Matrix.diagonal (fun i : Ω => (Real.exp (-(t * hA.eigenvalues i)) : ℂ)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp (scalar_euler_limit hr _)
    · simpa only [Matrix.diagonal_apply_ne _ hij] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => U) atTop (𝓝 U)).mul hd).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => star U) atTop (𝓝 (star U)))
  change Tendsto
    (fun n : ℕ => U * Matrix.diagonal (fun i : Ω => (((1 - r n * hA.eigenvalues i) ^ n : ℝ) : ℂ)) * star U)
    atTop (𝓝 (U * Matrix.diagonal (fun i : Ω => (Real.exp (-(t * hA.eigenvalues i)) : ℂ)) * star U)) at h
  convert h using 1
  · funext n
    rw [step_power_eq_cfc hA, hA.cfc_eq]
    rfl
  · rw [exp_neg_smul_eq_cfc hA, hA.cfc_eq]
    rfl

theorem poisson_step_coefficient_limit (t Λ : ℝ) :
    Tendsto (fun n : ℕ => n * ((t / n) * Real.exp (-Λ * (t / n)))) atTop (𝓝 t) := by
  have hdiv : Tendsto (fun n : ℕ => t / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => Real.exp (-Λ * (t / n))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp (hdiv.const_mul (-Λ))
  have h := he.const_mul t
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  field_simp

theorem poisson_matrix_euler_limit {A : Matrix Ω Ω ℂ} (hA : A.IsHermitian) (t Λ : ℝ) :
    Tendsto (fun n : ℕ => (1 - ((t / n) * Real.exp (-Λ * (t / n))) • A) ^ n)
      atTop (𝓝 (NormedSpace.exp ((-t) • A))) :=
  matrix_euler_limit hA (poisson_step_coefficient_limit t Λ)

end ExceptionalTimes.EulerSemigroup

#print axioms ExceptionalTimes.EulerSemigroup.matrix_euler_limit
#print axioms ExceptionalTimes.EulerSemigroup.poisson_matrix_euler_limit
