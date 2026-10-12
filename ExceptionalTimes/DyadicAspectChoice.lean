import ExceptionalTimes.DyadicScaleRounding
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! A two-time static exponent 9/4 beats the annular summation threshold
2+1/8, even when the aspect ratio is required to be a power of two. -/

open Filter
open scoped Topology

namespace ExceptionalTimes.DyadicAspectChoice

open DyadicScaleRounding

theorem exists_aspect (C : ℝ) : ∃ M : ℕ,2≤M ∧ IsDyadic M ∧
    C*(M : ℝ)^(-(9/4 : ℝ)) < (2*(M : ℝ))^(-(17/8 : ℝ))/4 := by
  have hp : Tendsto (fun n : ℕ => (2 : ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim : Tendsto (fun n : ℕ => C*((2 : ℝ)^n)^(-(1/8 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/8)).comp hp).const_mul C
  have he := (tendsto_order.1 hlim).2 ((2 : ℝ)^(-(17/8 : ℝ))/4) (by positivity)
  obtain ⟨n,hn,hn1⟩ := (he.and (eventually_ge_atTop 1)).exists
  refine ⟨2^n,?_,⟨n,rfl⟩,?_⟩
  · exact (show 2^1≤2^n from Nat.pow_le_pow_right (by norm_num) hn1)
  · have hM : (0 : ℝ)<(2^n : ℕ) := by positivity
    have hsmall : C*((2^n : ℕ) : ℝ)^(-(1/8 : ℝ)) < (2 : ℝ)^(-(17/8 : ℝ))/4 := by
      exact_mod_cast hn
    calc
      _ = (C*((2^n : ℕ) : ℝ)^(-(1/8 : ℝ)))*((2^n : ℕ) : ℝ)^(-(17/8 : ℝ)) := by
        rw [mul_assoc,← Real.rpow_add hM]
        norm_num
      _ < ((2 : ℝ)^(-(17/8 : ℝ))/4)*((2^n : ℕ) : ℝ)^(-(17/8 : ℝ)) :=
        mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hM _)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hM.le]
        ring

#print axioms exists_aspect

end ExceptionalTimes.DyadicAspectChoice
