import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The analytic implication from a radial estimate to finite time energy

This file formalizes an intermediate implication, not the percolation theorem.
The two-time radial estimate is an explicit hypothesis. In particular, this
file does not establish that estimate from published percolation results.
-/

open MeasureTheory Set
open scoped Interval

namespace ExceptionalTimes

/-- Explicit positive losses in the spatial exponents produce an arbitrarily
small positive loss in the time exponent. One may take
`η = δ / (8 * (1 + δ))` and `ζ = δ / 8`. -/
theorem exists_scale_exponent_losses {δ : ℝ} (hδ : 0 < δ) :
    ∃ η ζ : ℝ, 0 < η ∧ η < 3 / 4 ∧ 0 < ζ ∧
      (5 / 48 + ζ) / (3 / 4 - η) < 5 / 36 + δ := by
  let η : ℝ := δ / (8 * (1 + δ))
  have hden : 0 < 8 * (1 + δ) := by positivity
  have hη : 0 < η := div_pos hδ hden
  have hηsmall : η < 1 / 8 := by
    apply (div_lt_iff₀ hden).mpr
    linarith
  have hηeq : η * (8 * (1 + δ)) = δ :=
    div_mul_cancel₀ δ hden.ne'
  refine ⟨η, δ / 8, hη, by linarith, by positivity, ?_⟩
  apply (div_lt_iff₀ (by linarith : 0 < 3 / 4 - η)).mpr
  nlinarith

/-- Scalar conversion of a decorrelation length bound and an inverse one-arm
bound into a time-power bound. Here `b` denotes the inverse one-arm factor.
The lemma is purely analytic: all three percolation estimates are explicit
hypotheses, and no stochastic or geometric fact is postulated globally. -/
theorem radial_time_bound_of_scale
    {q a b m t A B D u v p : ℝ}
    (ht : 0 < t) (ht_one : t ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hm : 0 ≤ m)
    (hu : 0 ≤ u)
    (hscale : m ≤ D * t ^ (-(1 / v)))
    (honearm : b ≤ B * m ^ u)
    (hradial : q ≤ A * a ^ 2 * b)
    (hexponent : u / v ≤ p) :
    q ≤ (A * B * D ^ u) * a ^ 2 * t ^ (-p) := by
  have hscale_power : m ^ u ≤ D ^ u * t ^ (-(u / v)) := by
    calc
      m ^ u ≤ (D * t ^ (-(1 / v))) ^ u :=
        Real.rpow_le_rpow hm hscale hu
      _ = D ^ u * t ^ (-(u / v)) := by
        rw [Real.mul_rpow hD (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
        congr 2
        ring
  have hcoef : 0 ≤ A * B * D ^ u * a ^ 2 := by positivity
  calc
    q ≤ A * a ^ 2 * (B * m ^ u) :=
      hradial.trans (mul_le_mul_of_nonneg_left honearm (by positivity))
    _ = (A * B * a ^ 2) * m ^ u := by ring
    _ ≤ (A * B * a ^ 2) * (D ^ u * t ^ (-(u / v))) :=
      mul_le_mul_of_nonneg_left hscale_power (by positivity)
    _ = (A * B * D ^ u) * a ^ 2 * t ^ (-(u / v)) := by ring
    _ ≤ (A * B * D ^ u) * a ^ 2 * t ^ (-p) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge ht ht_one (neg_le_neg hexponent)) hcoef

/-- The elementary absorption used after the pivotal-cell variance estimate. -/
theorem radial_absorption {q a ε : ℝ} (hq : 0 ≤ q) (hε : ε ≤ 1 / 2)
    (h : q ≤ a ^ 2 + ε * q) : q ≤ 2 * a ^ 2 := by
  nlinarith [mul_le_mul_of_nonneg_right hε hq]

/-- On the unit interval the integrable power majorant has its usual exact
integral. The strict inequality excludes the logarithmically divergent case. -/
theorem power_integral_unit {p : ℝ} (hp : p < 1) :
    (∫ t in Ioo (0 : ℝ) 1, t ^ (-p)) = 1 / (1 - p) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by linarith : -1 < -p))]
  have hne : -p + 1 ≠ 0 := by linarith
  simp only [Real.one_rpow, Real.zero_rpow hne, sub_zero]
  congr 1
  ring

/-- A nonnegative measurable correlation with a power upper bound has finite
weighted energy whenever the two exponents have sum less than one. -/
theorem radial_energy_of_power_bound
    {q : ℝ → ℝ} {C a p γ : ℝ}
    (hq : Measurable q)
    (hq_nonneg : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ q t)
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, q t ≤ C * a ^ 2 * t ^ (-p))
    (hexponent : γ + p < 1) :
    IntegrableOn (fun t : ℝ => t ^ (-γ) * q t) (Ioo 0 1) ∧
      (∫ t in Ioo (0 : ℝ) 1, t ^ (-γ) * q t) ≤
        C * a ^ 2 / (1 - (γ + p)) := by
  have hmajorant : IntegrableOn
      (fun t : ℝ => C * a ^ 2 * t ^ (-(γ + p))) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)).const_mul _
  have hdom : ∀ t ∈ Ioo (0 : ℝ) 1,
      t ^ (-γ) * q t ≤ C * a ^ 2 * t ^ (-(γ + p)) := by
    intro t ht
    calc
      t ^ (-γ) * q t ≤ t ^ (-γ) * (C * a ^ 2 * t ^ (-p)) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (Real.rpow_nonneg ht.1.le _)
      _ = C * a ^ 2 * t ^ (-(γ + p)) := by
        rw [show -(γ + p) = -γ + -p by ring, Real.rpow_add ht.1]
        ring
  have hint : IntegrableOn (fun t : ℝ => t ^ (-γ) * q t) (Ioo 0 1) := by
    apply hmajorant.mono' ((measurable_id.pow_const (-γ)).mul hq).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change ‖t ^ (-γ) * q t‖ ≤ C * a ^ 2 * t ^ (-(γ + p))
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (hq_nonneg t ht))]
    exact hdom t ht
  refine ⟨hint, ?_⟩
  calc
    (∫ t in Ioo (0 : ℝ) 1, t ^ (-γ) * q t) ≤
        ∫ t in Ioo (0 : ℝ) 1, C * a ^ 2 * t ^ (-(γ + p)) :=
      setIntegral_mono_on hint hmajorant measurableSet_Ioo hdom
    _ = C * a ^ 2 / (1 - (γ + p)) := by
      rw [integral_const_mul, power_integral_unit hexponent]
      ring

/-- Every exponent strictly below `31/36` leaves room for a positive loss in
the proposed `5/36` correlation exponent. -/
theorem exists_radial_exponent_loss {γ : ℝ} (hγ : γ < 31 / 36) :
    ∃ δ : ℝ, 0 < δ ∧ γ + (5 / 36 + δ) < 1 := by
  refine ⟨(31 / 36 - γ) / 2, ?_, ?_⟩ <;> linarith

/-- The proposed radial two-time bound implies finite `γ`-energy for every
`γ < 31/36`. The existence of the radial bound remains a hypothesis. -/
theorem finite_energy_below_thirty_one_over_thirty_six
    {q : ℝ → ℝ} {a γ : ℝ}
    (hq : Measurable q)
    (hq_nonneg : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ q t)
    (hradial : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        q t ≤ C * a ^ 2 * t ^ (-(5 / 36 + δ)))
    (hγ : γ < 31 / 36) :
    IntegrableOn (fun t : ℝ => t ^ (-γ) * q t) (Ioo 0 1) ∧
      ∃ K : ℝ, 0 ≤ K ∧
        (∫ t in Ioo (0 : ℝ) 1, t ^ (-γ) * q t) ≤ K * a ^ 2 := by
  obtain ⟨δ, hδ, hexponent⟩ := exists_radial_exponent_loss hγ
  obtain ⟨C, hC, hbound⟩ := hradial δ hδ
  obtain ⟨hint, henergy⟩ := radial_energy_of_power_bound hq hq_nonneg hbound hexponent
  refine ⟨hint, C / (1 - (γ + (5 / 36 + δ))), ?_, ?_⟩
  · exact div_nonneg hC (by linarith)
  · convert henergy using 1
    ring

/-- Uniformity in an arbitrary radius index is preserved: the same energy
constant works for every member of a family with a uniform radial bound.
This is the version needed before an occupation-measure compactness argument.
No occupation measure, percolation process, or Hausdorff dimension is defined
or constructed by this theorem. -/
theorem uniform_energy_below_thirty_one_over_thirty_six
    {ι : Type*} {q : ι → ℝ → ℝ} {a : ι → ℝ} {γ : ℝ}
    (hq : ∀ i, Measurable (q i))
    (hq_nonneg : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ q i t)
    (hradial : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1,
        q i t ≤ C * (a i) ^ 2 * t ^ (-(5 / 36 + δ)))
    (hγ : γ < 31 / 36) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i,
      IntegrableOn (fun t : ℝ => t ^ (-γ) * q i t) (Ioo 0 1) ∧
      (∫ t in Ioo (0 : ℝ) 1, t ^ (-γ) * q i t) ≤ K * (a i) ^ 2 := by
  obtain ⟨δ, hδ, hexponent⟩ := exists_radial_exponent_loss hγ
  obtain ⟨C, hC, hbound⟩ := hradial δ hδ
  refine ⟨C / (1 - (γ + (5 / 36 + δ))), div_nonneg hC (by linarith), ?_⟩
  intro i
  obtain ⟨hint, henergy⟩ :=
    radial_energy_of_power_bound (hq i) (hq_nonneg i) (hbound i) hexponent
  refine ⟨hint, ?_⟩
  convert henergy using 1
  ring

end ExceptionalTimes

#print axioms ExceptionalTimes.exists_scale_exponent_losses
#print axioms ExceptionalTimes.radial_time_bound_of_scale
#print axioms ExceptionalTimes.radial_absorption
#print axioms ExceptionalTimes.power_integral_unit
#print axioms ExceptionalTimes.radial_energy_of_power_bound
#print axioms ExceptionalTimes.finite_energy_below_thirty_one_over_thirty_six
#print axioms ExceptionalTimes.uniform_energy_below_thirty_one_over_thirty_six
