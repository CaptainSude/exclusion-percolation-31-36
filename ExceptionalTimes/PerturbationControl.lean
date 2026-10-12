import ExceptionalTimes.BlockExpansion

/-! Quantitative finite-product linearization. A common centered-kernel
bound is propagated through the exact block expansion. The geometric bound
is an explicit hypothesis; no percolation estimate is asserted here. -/

namespace ExceptionalTimes.PerturbationControl

open CenteredBlocks BlockExpansion
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] {H : I → Type*} [∀ i, Fintype (H i)]

theorem selectedKernel_empty (p r : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) :
    selectedKernel p r ∅ f = kernel p f := by
  rw [selectedKernel_eq_kernel]
  simp

theorem exact_remainder_expansion (p r : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) :
    kernel (fun i h => p i h + r i h) f - kernel p f =
      ∑ S ∈ (Finset.univ : Finset (Finset I)).erase ∅, selectedKernel p r S f := by
  have hsum := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset I)))
    (f := fun S => selectedKernel p r S f) (Finset.mem_univ (∅ : Finset I))
  rw [selectedKernel_empty] at hsum
  rw [kernel_add_expansion]
  linarith

theorem scalar_remainder_sum (A B : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset I)).erase ∅,
      B ^ S.card * A ^ Sᶜ.card) = (A + B) ^ Fintype.card I - A ^ Fintype.card I := by
  have hsum := Fintype.prod_add (fun _ : I => B) (fun _ : I => A)
  simp only [Finset.prod_const, Finset.card_univ] at hsum
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset I)))
    (f := fun S => B ^ S.card * A ^ Sᶜ.card) (Finset.mem_univ (∅ : Finset I))
  simp only [Finset.card_empty, pow_zero, Finset.compl_empty, Finset.card_univ, one_mul] at hsplit
  rw [add_comm A B]
  linarith

/-- A single bound for arbitrary centered insertions controls every remainder
term. This is stronger than multiplying the number of blocks by a local error:
the same geometric factor M survives the entire expansion. -/
theorem centered_product_remainder_bound
    (p r : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ)
    (hp : ∀ i, ∑ h, p i h = 0) (hr : ∀ i, ∑ h, r i h = 0)
    {A B M : ℝ} (hM : 0 ≤ M)
    (hvp : ∀ i, variation (p i) ≤ A) (hvr : ∀ i, variation (r i) ≤ B)
    (hkernel : ∀ w : ∀ i, H i → ℝ, (∀ i, ∑ h, w i h = 0) →
      |kernel w f| ≤ M * ∏ i, variation (w i)) :
    |kernel (fun i h => p i h + r i h) f - kernel p f| ≤
      M * ((A + B) ^ Fintype.card I - A ^ Fintype.card I) := by
  rw [exact_remainder_expansion, ← scalar_remainder_sum (I := I), Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro S _
  rw [selectedKernel_eq_kernel]
  have hc : ∀ i, ∑ h, (if i ∈ S then r i h else p i h) = 0 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hi, hp, hr]
  apply (hkernel _ hc).trans
  apply mul_le_mul_of_nonneg_left _ hM
  have hv : (∏ i, variation (fun h => if i ∈ S then r i h else p i h)) ≤
      ∏ i, (if i ∈ S then B else A) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.sum_nonneg (fun h _ => abs_nonneg _)
    · intro i _
      by_cases hi : i ∈ S
      · simpa only [ite_eq_left hi] using hvr i
      · simpa only [ite_eq_right hi] using hvp i
  apply hv.trans_eq
  rw [Finset.prod_ite]
  have heq : Finset.univ.filter (fun i => i ∉ S) = Sᶜ := by ext i; simp
  rw [heq]
  simp

theorem power_remainder_bound {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) :
    (A + B) ^ k - A ^ k ≤ B * k * (A + B) ^ (k - 1) := by
  have h := abs_pow_sub_pow_le (a := A + B) (b := A) (n := k)
  rw [add_sub_cancel_left, abs_of_nonneg hB, abs_of_nonneg (add_nonneg hA hB),
    abs_of_nonneg hA, max_eq_left (le_add_of_nonneg_right hB)] at h
  exact (le_abs_self _).trans h

/-- The degree-dependent factor k is explicit. A summable forest coefficient
bound can therefore absorb all repeated-update remainders uniformly. -/
theorem centered_product_remainder_bound_linear
    (p r : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ)
    (hp : ∀ i, ∑ h, p i h = 0) (hr : ∀ i, ∑ h, r i h = 0)
    {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hvp : ∀ i, variation (p i) ≤ A) (hvr : ∀ i, variation (r i) ≤ B)
    (hkernel : ∀ w : ∀ i, H i → ℝ, (∀ i, ∑ h, w i h = 0) →
      |kernel w f| ≤ M * ∏ i, variation (w i)) :
    |kernel (fun i h => p i h + r i h) f - kernel p f| ≤
      M * (B * Fintype.card I * (A + B) ^ (Fintype.card I - 1)) :=
  (centered_product_remainder_bound p r f hp hr hM hvp hvr hkernel).trans
    (mul_le_mul_of_nonneg_left (power_remainder_bound hA hB _) hM)

end ExceptionalTimes.PerturbationControl

#print axioms ExceptionalTimes.PerturbationControl.centered_product_remainder_bound
#print axioms ExceptionalTimes.PerturbationControl.centered_product_remainder_bound_linear
