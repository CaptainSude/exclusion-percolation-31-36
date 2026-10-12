import ExceptionalTimes.CenteredBlocks
import Mathlib.Analysis.Complex.Exponential

/-! Exact expansion of finite independent block laws into centered signed
insertions. This is finite algebra; the geometric forest bounds and sewing
limits required to pass to a continuum limit are separate obligations. -/

namespace ExceptionalTimes.BlockExpansion

open scoped BigOperators Classical
open CenteredBlocks

variable {I : Type*} [Fintype I] {H : I → Type*} [∀ i, Fintype (H i)]

noncomputable def selectedKernel (p u : ∀ i, H i → ℝ) (S : Finset I)
    (f : (∀ i, H i) → ℝ) : ℝ :=
  ∑ h, ((∏ i ∈ S, u i (h i)) * (∏ i ∈ Sᶜ, p i (h i))) * f h

theorem selectedKernel_eq_kernel (p u : ∀ i, H i → ℝ) (S : Finset I)
    (f : (∀ i, H i) → ℝ) :
    selectedKernel p u S f = kernel (fun i h => if i ∈ S then u i h else p i h) f := by
  unfold selectedKernel kernel
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  rw [Finset.prod_ite]
  have heq : Finset.univ.filter (fun i => i ∉ S) = Sᶜ := by ext i; simp
  rw [heq]
  simp

theorem kernel_add_expansion (p u : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) :
    kernel (fun i h => p i h + u i h) f = ∑ S : Finset I, selectedKernel p u S f := by
  unfold kernel selectedKernel
  simp_rw [add_comm (p _ _) (u _ _), Fintype.prod_add, Finset.sum_mul]
  exact Finset.sum_comm

theorem selectedKernel_smul (p u : ∀ i, H i → ℝ) (S : Finset I)
    (f : (∀ i, H i) → ℝ) (τ : ℝ) :
    selectedKernel p (fun i h => τ * u i h) S f = τ ^ S.card * selectedKernel p u S f := by
  unfold selectedKernel
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- The exact finite polynomial whose coefficients are the selected signed
history kernels. No positivity or monotonicity of the tested function is used. -/
theorem kernel_scaled_expansion (p u : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) (τ : ℝ) :
    kernel (fun i h => p i h + τ * u i h) f =
      ∑ S : Finset I, τ ^ S.card * selectedKernel p u S f := by
  rw [kernel_add_expansion]
  simp_rw [selectedKernel_smul]

/-- The base law is normalized and each perturbation is centered. Thus the
expanded product still has mass one, even if it is viewed as a signed law. -/
theorem kernel_add_mass (p u : ∀ i, H i → ℝ)
    (hp : ∀ i, ∑ h, p i h = 1) (hu : ∀ i, ∑ h, u i h = 0) :
    kernel (fun i h => p i h + u i h) (fun _ => 1) = 1 := by
  unfold kernel
  simp_rw [mul_one]
  rw [← Fintype.prod_sum (fun i h => p i h + u i h)]
  simp [Finset.sum_add_distrib, hp, hu]

theorem variation_smul {A : Type*} [Fintype A] (u : A → ℝ) (τ : ℝ) :
    variation (fun h => τ * u h) = |τ| * variation u := by
  simp only [variation, abs_mul, Finset.mul_sum]

theorem variation_add {A : Type*} [Fintype A] (u w : A → ℝ) :
    variation (fun h => u h + w h) ≤ variation u + variation w := by
  unfold variation
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun h _ => abs_add_le _ _)

theorem refresh_time_remainder {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |(1 - Real.exp (-t)) - t| ≤ t ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -t)
    (by simpa only [abs_neg, abs_of_nonneg ht] using ht1)
  calc
    |(1 - Real.exp (-t)) - t| = |-(Real.exp (-t) - 1 - (-t))| := by
      congr 1
      ring
    _ = |Real.exp (-t) - 1 - (-t)| := abs_neg _
    _ ≤ t ^ 2 := by simpa only [neg_sq] using h

/-- This quadratic variation bound applies to the actual canonical pair
semigroup once its exact scalar coefficient 1-exp(-t) is identified. -/
theorem canonical_remainder_variation {A : Type*} [Fintype A] (u : A → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    variation (fun h => ((1 - Real.exp (-t)) - t) * u h) ≤ t ^ 2 * variation u := by
  rw [variation_smul]
  exact mul_le_mul_of_nonneg_right (refresh_time_remainder ht ht1)
    (Finset.sum_nonneg fun h _ => abs_nonneg (u h))

end ExceptionalTimes.BlockExpansion

#print axioms ExceptionalTimes.BlockExpansion.kernel_scaled_expansion
#print axioms ExceptionalTimes.BlockExpansion.canonical_remainder_variation
