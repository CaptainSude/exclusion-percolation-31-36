import ExceptionalTimes.FiniteGenerator
import FractionalComparison
import Mathlib.Analysis.Matrix.Order

/-!
# Fractional comparison for the actual finite swap matrices

The matrix order is explicitly the positive-semidefinite (Loewner) order,
and the C-star norm is explicitly the Euclidean operator norm. We first
transport the proved real generator positivity to complex matrices, then
apply mathlib's fractional inverse order theorem to these same matrices.
The time-correlation/Laplace identification is a separate remaining step.
-/

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace ExceptionalTimes.FiniteFractional

open ExceptionalTimes.FiniteGenerator

variable {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]

/-- Real positive semidefiniteness survives complexification. The proof
uses an actual Gram factor, so this does not postulate an order bridge. -/
theorem posSemidef_complexification {A : Matrix Ω Ω ℝ} (hA : A.PosSemidef) :
    (A.map Complex.ofReal).PosSemidef := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hstar : (star B).map Complex.ofReal = star (B.map Complex.ofReal) := by
    ext i j
    simp [Matrix.star_eq_conjTranspose]
  change ((star B * B).map Complex.ofRealHom).PosSemidef
  rw [Matrix.map_mul]
  change ((star B).map Complex.ofReal * B.map Complex.ofReal).PosSemidef
  rw [hstar]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The literal real swap generator, viewed as a complex matrix. -/
noncomputable def complexGenerator (σ : I → Equiv.Perm Ω) (rate : I → ℝ) :
    Matrix Ω Ω ℂ := (generatorMatrix σ rate).map Complex.ofReal

theorem complexGenerator_nonneg (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ)
    (hr : ∀ i, 0 ≤ rate i) : 0 ≤ complexGenerator σ rate :=
  (posSemidef_complexification (generatorMatrix_posSemidef σ hσ rate hr)).nonneg

omit [Fintype Ω] in
theorem complexGenerator_sub_rates (σ : I → Equiv.Perm Ω) (r s : I → ℝ) :
    complexGenerator σ s - complexGenerator σ r =
      complexGenerator σ (fun i => s i - r i) := by
  ext ω η
  simp only [complexGenerator, Matrix.sub_apply, Matrix.map_apply]
  rw [← Complex.ofReal_sub]
  exact congrArg Complex.ofReal (congrFun (congrFun (generatorMatrix_sub_rates σ r s) ω) η)

/-- Pointwise domination of the actual edge rates implies Loewner order. -/
theorem complexGenerator_mono (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) {r s : I → ℝ}
    (hrs : ∀ i, r i ≤ s i) : complexGenerator σ r ≤ complexGenerator σ s := by
  apply Matrix.le_iff.mpr
  rw [complexGenerator_sub_rates]
  exact Matrix.nonneg_iff_posSemidef.mp
    (complexGenerator_nonneg σ hσ _ (fun i => sub_nonneg.mpr (hrs i)))

omit [Fintype Ω] in
theorem complexGenerator_scale (σ : I → Equiv.Perm Ω) (r : I → ℝ) (c : ℝ) :
    complexGenerator σ (fun i => c * r i) = c • complexGenerator σ r := by
  ext ω η
  simp [complexGenerator, generatorMatrix, Finset.mul_sum, mul_assoc,
    Complex.real_smul]

/-- The shift-one fractional resolvents of finite swap generators reverse
the proved rate domination. Zero modes cause no invertibility problem. -/
theorem shifted_fractional_rate_comparison (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) {r₀ r₁ : I → ℝ} {c s : ℝ}
    (hs : s ∈ Set.Icc 0 1) (hc : 0 ≤ c) (hr₀ : ∀ i, 0 ≤ r₀ i)
    (hr : ∀ i, c * r₀ i ≤ r₁ i) :
    CFC.rpow (Ring.inverse (1 + complexGenerator σ r₁)) s ≤
      CFC.rpow (Ring.inverse (1 + c • complexGenerator σ r₀)) s := by
  rw [← complexGenerator_scale]
  exact ExceptionalTimesPilot.shifted_fractional_inverse_order hs
    isStrictlyPositive_one
    (complexGenerator_nonneg σ hσ _ (fun i => mul_nonneg hc (hr₀ i)))
    (complexGenerator_mono σ hσ hr)

omit [DecidableEq Ω] in
/-- Loewner comparison controls the literal finite quadratic forms. -/
theorem quadraticForm_mono {A B : Matrix Ω Ω ℂ} (hAB : A ≤ B) (f : Ω → ℂ) :
    star f ⬝ᵥ (A *ᵥ f) ≤ star f ⬝ᵥ (B *ᵥ f) := by
  have h := (Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg f
  simpa only [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using h

/-- The normalized real quadratic form uses the actual uniform state law. -/
noncomputable def uniformQuadraticForm (A : Matrix Ω Ω ℂ) (f : Ω → ℂ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * (star f ⬝ᵥ (A *ᵥ f)).re

omit [DecidableEq Ω] in
theorem uniformQuadraticForm_mono {A B : Matrix Ω Ω ℂ}
    (hAB : A ≤ B) (f : Ω → ℂ) :
    uniformQuadraticForm A f ≤ uniformQuadraticForm B f := by
  apply mul_le_mul_of_nonneg_left (Complex.le_def.mp (quadraticForm_mono hAB f)).1
  positivity

theorem fractional_uniform_energy_comparison (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) {r₀ r₁ : I → ℝ} {c s : ℝ}
    (hs : s ∈ Set.Icc 0 1) (hc : 0 ≤ c) (hr₀ : ∀ i, 0 ≤ r₀ i)
    (hr : ∀ i, c * r₀ i ≤ r₁ i) (f : Ω → ℂ) :
    uniformQuadraticForm (CFC.rpow (Ring.inverse (1 + complexGenerator σ r₁)) s) f ≤
    uniformQuadraticForm (CFC.rpow (Ring.inverse (1 + c • complexGenerator σ r₀)) s) f :=
  uniformQuadraticForm_mono
    (shifted_fractional_rate_comparison σ hσ hs hc hr₀ hr) f

section ColorSwaps

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The comparison specialized to genuine finite color exchanges. -/
theorem colorSwap_fractional_rate_comparison (edge : I → V × V)
    {r₀ r₁ : I → ℝ} {c s : ℝ} (hs : s ∈ Set.Icc 0 1) (hc : 0 ≤ c)
    (hr₀ : ∀ i, 0 ≤ r₀ i) (hr : ∀ i, c * r₀ i ≤ r₁ i) :
    CFC.rpow (Ring.inverse
      (1 + complexGenerator (fun i => colorSwap (edge i).1 (edge i).2) r₁)) s ≤
    CFC.rpow (Ring.inverse
      (1 + c • complexGenerator (fun i => colorSwap (edge i).1 (edge i).2) r₀)) s :=
  shifted_fractional_rate_comparison _ (fun _ => colorSwap_involutive _ _)
    hs hc hr₀ hr

/-- Unit swaps dominate half-rate swaps on any selected edge subfamily.
For a selected disjoint matching, these half-rate swaps are precisely its
rate-one canonical pair refreshes. The comparison itself does not require
the selected edges to be disjoint. -/
theorem unit_swap_dominates_half_rate_subfamily (edge : I → V × V)
    (selected : I → Bool) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (f : (V → Bool) → ℂ) :
    uniformQuadraticForm (CFC.rpow (Ring.inverse
      (1 + complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
        (fun _ => 1))) s) f ≤
    uniformQuadraticForm (CFC.rpow (Ring.inverse
      (1 + complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
        (fun i => if selected i then (1 / 2 : ℝ) else 0))) s) f := by
  have hr₀ : ∀ i, 0 ≤ (if selected i then (1 / 2 : ℝ) else 0) := by
    intro i
    split <;> norm_num
  have hr : ∀ i, (1 : ℝ) * (if selected i then (1 / 2 : ℝ) else 0) ≤ 1 := by
    intro i
    split <;> norm_num
  simpa only [one_smul] using fractional_uniform_energy_comparison
    (fun i => colorSwap (edge i).1 (edge i).2)
    (fun _ => colorSwap_involutive _ _) hs (by norm_num : (0 : ℝ) ≤ 1)
    hr₀ hr f

end ColorSwaps

#print axioms posSemidef_complexification
#print axioms complexGenerator_mono
#print axioms shifted_fractional_rate_comparison
#print axioms fractional_uniform_energy_comparison
#print axioms colorSwap_fractional_rate_comparison
#print axioms unit_swap_dominates_half_rate_subfamily

end ExceptionalTimes.FiniteFractional
