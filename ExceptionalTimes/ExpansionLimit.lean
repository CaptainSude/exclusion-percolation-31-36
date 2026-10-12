import ExceptionalTimes.BlockExpansion
import ExceptionalTimes.ForestCounting
import Mathlib.Analysis.Normed.Group.Tannery

/-! Degree grouping for the actual finite block product, followed by
dominated summation using the proved superfactorial forest majorant. -/

namespace ExceptionalTimes.ExpansionLimit

open BlockExpansion CenteredBlocks Filter
open scoped BigOperators Classical Topology

variable {I : Type*} [Fintype I] {H : I → Type*} [∀ i, Fintype (H i)]

noncomputable def coefficient (p u : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ)
    (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset I)).filter (fun S => S.card = k), selectedKernel p u S f

theorem coefficient_eq_zero_of_card_lt (p u : ∀ i, H i → ℝ)
    (f : (∀ i, H i) → ℝ) {k : ℕ} (hk : Fintype.card I < k) : coefficient p u f k = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  have heq := (Finset.mem_filter.mp hS).2
  exact False.elim ((not_lt_of_ge S.card_le_univ) (heq ▸ hk))

theorem kernel_eq_sum_coefficients (p u : ∀ i, H i → ℝ)
    (f : (∀ i, H i) → ℝ) (τ : ℝ) :
    kernel (fun i h => p i h + τ * u i h) f =
      ∑ k ∈ Finset.range (Fintype.card I + 1), τ ^ k * coefficient p u f k := by
  rw [kernel_scaled_expansion]
  have hmap : ∀ S ∈ (Finset.univ : Finset (Finset I)), S.card ∈ Finset.range (Fintype.card I + 1) :=
    fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le S.card_le_univ)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro k _
  unfold coefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [(Finset.mem_filter.mp hS).2]

theorem kernel_eq_tsum_coefficients (p u : ∀ i, H i → ℝ)
    (f : (∀ i, H i) → ℝ) (τ : ℝ) :
    kernel (fun i h => p i h + τ * u i h) f = ∑' k : ℕ, τ ^ k * coefficient p u f k := by
  rw [kernel_eq_sum_coefficients]
  symm
  apply tsum_eq_sum
  intro k hk
  rw [coefficient_eq_zero_of_card_lt p u f
    (by simpa only [Finset.mem_range, not_lt, Nat.add_one_le_iff] using hk), mul_zero]

theorem summable_degree_superfactor {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β) :
    Summable (fun k : ℕ => k * A ^ k * (k : ℝ) ^ (-β * k)) := by
  apply (ForestCounting.summable_superfactor
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA) hβ).of_norm_bounded
  intro k
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.le_of_lt k.lt_two_pow_self)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((2 : ℝ) ^ k * A ^ k) * (k : ℝ) ^ (-β * k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (pow_nonneg hA _))
        (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    _ = _ := by rw [mul_pow]

/-- This is the limit step used once fixed-degree sewing and the common
forest bound have been supplied. The coefficient family may have different
finite support at each mesh; there is no fixed truncation assumption. -/
theorem tendsto_tsum_zero_of_forest_bound
    {Mesh : Type*} (l : Filter Mesh) (a : Mesh → ℕ → ℝ)
    {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (hdegree : ∀ k, Tendsto (fun e => a e k) l (𝓝 0))
    (hbound : ∀ᶠ e in l, ∀ k, |a e k| ≤ A ^ k * (k : ℝ) ^ (-β * k)) :
    Tendsto (fun e => ∑' k, a e k) l (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (ForestCounting.summable_superfactor hA hβ) hdegree
    (hbound.mono fun _ he k => by simpa only [Real.norm_eq_abs] using he k)
  simpa using h

end ExceptionalTimes.ExpansionLimit

#print axioms ExceptionalTimes.ExpansionLimit.kernel_eq_tsum_coefficients
#print axioms ExceptionalTimes.ExpansionLimit.tendsto_tsum_zero_of_forest_bound
