import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
The exact deterministic rate hypotheses of the proposed theorem, and
normalization to the symmetric transition-matrix convention in
Garban--Vanneuville, Definition 1.1 and Proposition 3.3.

No stochastic process is asserted to exist in this file. In particular,
normalizing the rates is not by itself the trajectory time-change theorem.
-/

namespace ExceptionalTimes

structure RateKernel where
  rate : (ℤ × ℤ) → ℝ
  nonneg : ∀ z, 0 ≤ rate z
  symmetric : ∀ z, rate (-z) = rate z
  diagonal : rate 0 = 0
  summable : Summable rate
  positive_mass : 0 < ∑' z, rate z

namespace RateKernel

noncomputable def mass (k : RateKernel) : ℝ := ∑' z, k.rate z

theorem mass_pos (k : RateKernel) : 0 < k.mass := k.positive_mass

theorem exists_positive_displacement (k : RateKernel) :
    ∃ z : ℤ × ℤ, z ≠ 0 ∧ 0 < k.rate z := by
  by_contra h
  have hzero : ∀ z, k.rate z = 0 := by
    intro z
    by_cases hz : z = 0
    · simpa [hz] using k.diagonal
    · have hnonpos : k.rate z ≤ 0 := by
        apply le_of_not_gt
        exact fun hpos => h ⟨z, hz, hpos⟩
      exact le_antisymm hnonpos (k.nonneg z)
  have hm := k.positive_mass
  simp only [hzero, tsum_zero, lt_self_iff_false] at hm

def pairRate (k : RateKernel) (x y : ℤ × ℤ) : ℝ := k.rate (y - x)

theorem pairRate_nonneg (k : RateKernel) (x y : ℤ × ℤ) :
    0 ≤ k.pairRate x y := k.nonneg _

theorem pairRate_symmetric (k : RateKernel) (x y : ℤ × ℤ) :
    k.pairRate x y = k.pairRate y x := by
  simpa only [pairRate, neg_sub] using k.symmetric (x - y)

theorem pairRate_diagonal (k : RateKernel) (x : ℤ × ℤ) :
    k.pairRate x x = 0 := by
  simp only [pairRate, sub_self, k.diagonal]

theorem pairRate_summable (k : RateKernel) (x : ℤ × ℤ) :
    Summable (k.pairRate x) := by
  exact (Equiv.subRight x).summable_iff.mpr k.summable

theorem pairRate_row_sum (k : RateKernel) (x : ℤ × ℤ) :
    (∑' y, k.pairRate x y) = k.mass :=
  (Equiv.subRight x).tsum_eq k.rate

noncomputable def normalizedRate (k : RateKernel) (z : ℤ × ℤ) : ℝ :=
  k.rate z / k.mass

theorem normalizedRate_sum (k : RateKernel) :
    (∑' z, k.normalizedRate z) = 1 := by
  simp only [normalizedRate, tsum_div_const]
  exact div_self (ne_of_gt k.mass_pos)

noncomputable def normalized (k : RateKernel) : RateKernel where
  rate := k.normalizedRate
  nonneg z := div_nonneg (k.nonneg z) k.mass_pos.le
  symmetric z := by simp only [normalizedRate, k.symmetric]
  diagonal := by simp only [normalizedRate, k.diagonal, zero_div]
  summable := k.summable.div_const k.mass
  positive_mass := by rw [k.normalizedRate_sum]; exact zero_lt_one

theorem normalized_mass (k : RateKernel) : k.normalized.mass = 1 :=
  k.normalizedRate_sum

theorem normalized_row_sum (k : RateKernel) (x : ℤ × ℤ) :
    (∑' y, k.normalized.pairRate x y) = 1 := by
  rw [k.normalized.pairRate_row_sum, k.normalized_mass]

theorem rate_from_normalized (k : RateKernel) (z : ℤ × ℤ) :
    k.mass * k.normalized.rate z = k.rate z := by
  change k.mass * (k.rate z / k.mass) = k.rate z
  rw [mul_comm]
  exact div_mul_cancel₀ _ (ne_of_gt k.mass_pos)

end RateKernel
end ExceptionalTimes

#print axioms ExceptionalTimes.RateKernel.exists_positive_displacement
#print axioms ExceptionalTimes.RateKernel.pairRate_row_sum
#print axioms ExceptionalTimes.RateKernel.normalized_row_sum
#print axioms ExceptionalTimes.RateKernel.rate_from_normalized
