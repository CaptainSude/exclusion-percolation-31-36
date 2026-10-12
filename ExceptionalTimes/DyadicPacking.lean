import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Scalar dyadic sums for buffered pivotal-cell estimates

The results here prove the real-power algebra and geometric-series summation
after inserting the stated cell-count and pivotal-probability estimates. They
do not prove geometric cell packing, arm extraction, or those probabilities.
All sums are over arbitrary finite sets of nonnegative dyadic indices.
-/

namespace ExceptionalTimes.DyadicPacking

open scoped BigOperators

noncomputable def dyadicFactor (exponent : ℝ) (i : ℕ) : ℝ :=
  (2 : ℝ) ^ (exponent * (i : ℝ))

/-- Explicit finite geometric-series bound, positive when `exponent < 0`. -/
noncomputable def dyadicConstant (exponent : ℝ) : ℝ :=
  (1 - (2 : ℝ) ^ exponent)⁻¹

theorem dyadicFactor_eq_pow (exponent : ℝ) (i : ℕ) :
    dyadicFactor exponent i = ((2 : ℝ) ^ exponent) ^ i := by
  rw [dyadicFactor, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

theorem dyadicFactor_nonneg (exponent : ℝ) (i : ℕ) :
    0 ≤ dyadicFactor exponent i := Real.rpow_nonneg (by norm_num) _

theorem dyadicConstant_pos {exponent : ℝ} (he : exponent < 0) :
    0 < dyadicConstant exponent := by
  exact inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) he))

theorem finite_dyadic_sum_le {exponent : ℝ} (he : exponent < 0) (I : Finset ℕ) :
    ∑ i ∈ I, dyadicFactor exponent i ≤ dyadicConstant exponent := by
  have hr0 : 0 ≤ (2 : ℝ) ^ exponent := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ exponent < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) he
  have hs := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum I
    (fun i _ => pow_nonneg hr0 i)
  simpa only [dyadicFactor_eq_pow, tsum_geometric_of_lt_one hr0 hr1,
    dyadicConstant] using hs

theorem weighted_finite_dyadic_sum_le {exponent weight : ℝ}
    (he : exponent < 0) (hw : 0 ≤ weight) (I : Finset ℕ) :
    ∑ i ∈ I, weight * dyadicFactor exponent i ≤ dyadicConstant exponent * weight := by
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (finite_dyadic_sum_le he I) hw).trans_eq
    (mul_comm _ _)

/-- The second index range may depend on the first, as it does when a boundary
scale imposes an upper cutoff on the outer dyadic distance. -/
theorem finite_double_dyadic_sum_le {first second weight : ℝ}
    (hf : first < 0) (hs : second < 0) (hw : 0 ≤ weight)
    (I : Finset ℕ) (J : ℕ → Finset ℕ) :
    (∑ i ∈ I, ∑ j ∈ J i,
      weight * dyadicFactor first i * dyadicFactor second j) ≤
      (dyadicConstant first * dyadicConstant second) * weight := by
  calc
    _ ≤ ∑ i ∈ I, dyadicConstant second * (weight * dyadicFactor first i) := by
      apply Finset.sum_le_sum
      intro i _
      exact weighted_finite_dyadic_sum_le hs
        (mul_nonneg hw (dyadicFactor_nonneg first i)) (J i)
    _ = ∑ i ∈ I, (dyadicConstant second * weight) * dyadicFactor first i := by
      simp only [mul_assoc]
    _ ≤ dyadicConstant first * (dyadicConstant second * weight) :=
      weighted_finite_dyadic_sum_le hf
        (mul_nonneg (dyadicConstant_pos hs).le hw) I
    _ = _ := by ring

noncomputable def sideConstant (b h lam : ℝ) : ℝ :=
  dyadicConstant (b - h) * dyadicConstant (1 - lam + b)

theorem sideConstant_pos {b h lam : ℝ} (hbh : b < h) (hlam : 1 + b < lam) :
    0 < sideConstant b h lam := by
  exact mul_pos (dyadicConstant_pos (sub_neg.mpr hbh))
    (dyadicConstant_pos (by linarith))

/-- The normalized double sum in BP3, with its full explicit positive constant. -/
theorem side_dyadic_sum_le {m a b h lam : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hbh : b < h) (hlam : 1 + b < lam) (I : Finset ℕ) (J : ℕ → Finset ℕ) :
    (∑ i ∈ I, ∑ j ∈ J i,
      (m / a) ^ b * dyadicFactor (b - h) i * dyadicFactor (1 - lam + b) j) ≤
      sideConstant b h lam * (m / a) ^ b :=
  finite_double_dyadic_sum_le (sub_neg.mpr hbh) (by linarith)
    (Real.rpow_nonneg (div_pos hm ha).le _) I J

/-- The corner classes have only the first decay factor. -/
theorem corner_dyadic_sum_le {m a b h : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hbh : b < h) (I : Finset ℕ) :
    (∑ i ∈ I, (m / a) ^ b * dyadicFactor (b - h) i) ≤
      dyadicConstant (b - h) * (m / a) ^ b :=
  weighted_finite_dyadic_sum_le (sub_neg.mpr hbh)
    (Real.rpow_nonneg (div_pos hm ha).le _) I

/-- Bulk shells first give exponent `h`. If `m ≤ r` and `b ≤ h`, the
bound weakens to the common boundary exponent `b`. -/
theorem bulk_dyadic_sum_le {m r b h : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hmr : m ≤ r) (hh : 0 < h) (hbh : b ≤ h) (I : Finset ℕ) :
    (∑ i ∈ I, (m / r) ^ h * dyadicFactor (-h) i) ≤
      dyadicConstant (-h) * (m / r) ^ b := by
  refine (weighted_finite_dyadic_sum_le (neg_neg_of_pos hh)
    (Real.rpow_nonneg (div_pos hm hr).le _) I).trans ?_
  apply mul_le_mul_of_nonneg_left _ (dyadicConstant_pos (neg_neg_of_pos hh)).le
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos hm hr)
    ((div_le_one hr).mpr hmr) hbh

/-- The original side-class counting factor multiplied by its pivotal cost. -/
noncomputable def sideWeight (m a d u b h lam : ℝ) : ℝ :=
  (d * u / m ^ 2) * (m / d) ^ (2 + h) * (d / u) ^ lam * (u / a) ^ b

/-- Exact real-power algebra; the dyadic normalization is derived, not assumed. -/
theorem sideWeight_normalized {m a d u : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hd : 0 < d) (hu : 0 < u) (b h lam : ℝ) :
    sideWeight m a d u b h lam =
      (m / a) ^ b * (d / m) ^ (b - h) * (u / d) ^ (1 - lam + b) := by
  unfold sideWeight
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Real.log_rpow]
  ring

noncomputable def dyadicScale (base : ℝ) (i : ℕ) : ℝ := base * (2 : ℝ) ^ i

theorem dyadicScale_pos {base : ℝ} (hb : 0 < base) (i : ℕ) :
    0 < dyadicScale base i := mul_pos hb (pow_pos (by norm_num) _)

theorem dyadicScale_div {base : ℝ} (hb : 0 < base) (i : ℕ) :
    dyadicScale base i / base = (2 : ℝ) ^ i := by
  unfold dyadicScale
  field_simp

theorem dyadicFactor_eq_natpow_rpow (exponent : ℝ) (i : ℕ) :
    dyadicFactor exponent i = ((2 : ℝ) ^ i) ^ exponent := by
  rw [dyadicFactor_eq_pow, Real.rpow_pow_comm (by norm_num)]

theorem sideWeight_dyadic {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (b h lam : ℝ) (i j : ℕ) :
    sideWeight m a (dyadicScale m i) (dyadicScale (dyadicScale m i) j) b h lam =
      (m / a) ^ b * dyadicFactor (b - h) i * dyadicFactor (1 - lam + b) j := by
  rw [sideWeight_normalized hm ha (dyadicScale_pos hm i)
      (dyadicScale_pos (dyadicScale_pos hm i) j),
    dyadicScale_div hm, dyadicScale_div (dyadicScale_pos hm i),
    ← dyadicFactor_eq_natpow_rpow, ← dyadicFactor_eq_natpow_rpow]

/-- BP3's original side-class weights, after the dyadic substitution. -/
theorem original_side_sum_le {m a b h lam : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hbh : b < h) (hlam : 1 + b < lam) (I : Finset ℕ) (J : ℕ → Finset ℕ) :
    (∑ i ∈ I, ∑ j ∈ J i,
      sideWeight m a (dyadicScale m i) (dyadicScale (dyadicScale m i) j) b h lam) ≤
      sideConstant b h lam * (m / a) ^ b := by
  simp_rw [sideWeight_dyadic hm ha]
  exact side_dyadic_sum_le hm ha hbh hlam I J

noncomputable def cornerWeight (m a d b h : ℝ) : ℝ :=
  (d ^ 2 / m ^ 2) * (m / d) ^ (2 + h) * (d / a) ^ b

theorem cornerWeight_normalized {m a d : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hd : 0 < d) (b h : ℝ) :
    cornerWeight m a d b h = (m / a) ^ b * (d / m) ^ (b - h) := by
  unfold cornerWeight
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Real.log_rpow]
  ring

theorem cornerWeight_dyadic {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (b h : ℝ) (i : ℕ) :
    cornerWeight m a (dyadicScale m i) b h = (m / a) ^ b * dyadicFactor (b - h) i := by
  rw [cornerWeight_normalized hm ha (dyadicScale_pos hm i), dyadicScale_div hm,
    ← dyadicFactor_eq_natpow_rpow]

theorem original_corner_sum_le {m a b h : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hbh : b < h) (I : Finset ℕ) :
    (∑ i ∈ I, cornerWeight m a (dyadicScale m i) b h) ≤
      dyadicConstant (b - h) * (m / a) ^ b := by
  simp_rw [cornerWeight_dyadic hm ha]
  exact corner_dyadic_sum_le hm ha hbh I

noncomputable def bulkWeight (m s h : ℝ) : ℝ :=
  (s / m) ^ (2 : ℕ) * (m / s) ^ (2 + h)

theorem bulkWeight_normalized {m r s : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hs : 0 < s) (h : ℝ) :
    bulkWeight m s h = (m / r) ^ h * (s / r) ^ (-h) := by
  unfold bulkWeight
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Real.log_rpow]
  ring

theorem bulkWeight_dyadic {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (h : ℝ) (i : ℕ) :
    bulkWeight m (dyadicScale r i) h = (m / r) ^ h * dyadicFactor (-h) i := by
  rw [bulkWeight_normalized hm hr (dyadicScale_pos hr i), dyadicScale_div hr,
    ← dyadicFactor_eq_natpow_rpow]

theorem original_bulk_sum_le {m r b h : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hmr : m ≤ r) (hh : 0 < h) (hbh : b ≤ h) (I : Finset ℕ) :
    (∑ i ∈ I, bulkWeight m (dyadicScale r i) h) ≤
      dyadicConstant (-h) * (m / r) ^ b := by
  simp_rw [bulkWeight_dyadic hm hr]
  exact bulk_dyadic_sum_le hm hr hmr hh hbh I

#print axioms side_dyadic_sum_le
#print axioms corner_dyadic_sum_le
#print axioms bulk_dyadic_sum_le
#print axioms sideWeight_normalized
#print axioms original_side_sum_le
#print axioms original_corner_sum_le
#print axioms original_bulk_sum_le

end ExceptionalTimes.DyadicPacking
