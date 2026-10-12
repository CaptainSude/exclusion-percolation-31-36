import ExceptionalTimes.RadialEnergy
import Mathlib.Algebra.Order.Floor.Semiring

/-! An explicit integer decorrelation scale from a power bound for
reference times. This is numerical: no dynamical mixing is assumed to
follow merely from choosing this scale. -/

namespace ExceptionalTimes.DecorrelationLength

noncomputable def roundedLength (base : ℕ) (C v t : ℝ) : ℕ :=
  base + ⌈(C/t)^v⁻¹⌉₊

theorem base_le_roundedLength (base : ℕ) (C v t : ℝ) :
    base≤roundedLength base C v t := Nat.le_add_right _ _

theorem reference_power_le_time {base : ℕ} (hbase : 0<base) {C v t : ℝ}
    (hC : 0≤C) (hv : 0<v) (ht : 0<t) {s : ℕ}
    (hs : roundedLength base C v t≤s) : C*(s : ℝ)^(-v)≤t := by
  have hs0 : (0 : ℝ)<s := by
    exact_mod_cast hbase.trans_le ((base_le_roundedLength base C v t).trans hs)
  have hceil : (C/t)^v⁻¹≤(s : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈(C/t)^v⁻¹⌉₊≤s by
      exact (Nat.le_add_left _ _).trans hs))
  have hp : C/t≤(s : ℝ)^v :=
    (Real.rpow_inv_le_iff_of_pos (div_nonneg hC ht.le) hs0.le hv).mp hceil
  rw [Real.rpow_neg hs0.le,← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hs0 v)).mpr
  exact (div_le_iff₀ ht).mp hp |>.trans_eq (mul_comm _ _)

theorem roundedLength_bound (base : ℕ) {C v t : ℝ} (hC : 0≤C)
    (hv : 0<v) (ht : 0<t) (ht1 : t≤1) :
    (roundedLength base C v t : ℝ)≤
      ((base : ℝ)+1+C^v⁻¹)*t^(-(1/v)) := by
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg (div_nonneg hC ht.le) v⁻¹)).le
  have hF : (C/t)^v⁻¹=C^v⁻¹*t^(-(1/v)) := by
    rw [Real.div_rpow hC ht.le,one_div,Real.rpow_neg ht.le]
    rfl
  have htp : 1≤t^(-(1/v)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1
      (show -(1/v)≤0 from neg_nonpos.mpr (one_div_nonneg.mpr hv.le))
    simpa only [Real.rpow_zero] using h
  have hmul := mul_le_mul_of_nonneg_left htp
    (by positivity : (0 : ℝ)≤(base : ℝ)+1)
  dsimp only [roundedLength]
  push_cast
  rw [hF] at hceil
  rw [hF]
  nlinarith only [hceil,hmul]

/-- The bound holds simultaneously at every larger spatial scale. -/
theorem exists_integer_scale (base : ℕ) (hbase : 0<base) {C v : ℝ}
    (hC : 0≤C) (hv : 0<v) (reference : ℕ→ℝ)
    (href : ∀ s,base≤s → reference s≤C*(s : ℝ)^(-v)) :
    ∃ D : ℝ,0≤D ∧ ∃ m : ℝ→ℕ,∀ t∈Set.Ioo (0 : ℝ) 1,
      base≤m t ∧ (m t : ℝ)≤D*t^(-(1/v)) ∧
        ∀ s,m t≤s → reference s≤t := by
  refine ⟨(base : ℝ)+1+C^v⁻¹,by positivity,roundedLength base C v,?_⟩
  intro t ht
  refine ⟨base_le_roundedLength base C v t,roundedLength_bound base hC hv ht.1 ht.2.le,?_⟩
  intro s hs
  exact (href s ((base_le_roundedLength base C v t).trans hs)).trans
    (reference_power_le_time hbase hC hv ht.1 hs)

#print axioms exists_integer_scale

end ExceptionalTimes.DecorrelationLength
