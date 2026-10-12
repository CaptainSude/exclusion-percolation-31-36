import ExceptionalTimes.RadialEnergy
import ExceptionalTimes.OccupationWitnesses

/-! The actual nonnegative correlation bound, with its normalization, implies
the time-lag energy hypothesis used by the occupation-measure argument.
The power bound is a new percolation obligation, not a published input. -/

namespace ExceptionalTimes.CorrelationPowerBound

open MeasureTheory Set
open scoped ENNReal

theorem normalized_pointwise_bound {a q : ℝ≥0∞} {C p γ t : ℝ}
    (ha : a ≠ 0) (hatop : a ≠ ⊤) (hC : 0 ≤ C) (ht : 0 < t)
    (hq : q ≤ ENNReal.ofReal C * a ^ 2 * ENNReal.ofReal (t ^ (-p))) :
    frostmanKernel γ 0 t * a⁻¹ ^ 2 * q ≤
      ENNReal.ofReal (C * t ^ (-(γ + p))) := by
  have hcancel : a⁻¹ ^ 2 * a ^ 2 = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel ha hatop, one_pow]
  have hk : frostmanKernel γ 0 t = ENNReal.ofReal (t ^ (-γ)) := by
    rw [frostmanKernel_off_diagonal γ (ne_of_lt ht), Real.dist_eq,
      zero_sub, abs_neg, abs_of_pos ht]
  calc
    frostmanKernel γ 0 t * a⁻¹ ^ 2 * q ≤
        frostmanKernel γ 0 t * a⁻¹ ^ 2 *
          (ENNReal.ofReal C * a ^ 2 * ENNReal.ofReal (t ^ (-p))) :=
      mul_le_mul' le_rfl hq
    _ = ENNReal.ofReal C * frostmanKernel γ 0 t * ENNReal.ofReal (t ^ (-p)) := by
      calc
        _ = ENNReal.ofReal C * frostmanKernel γ 0 t *
            (a⁻¹ ^ 2 * a ^ 2) * ENNReal.ofReal (t ^ (-p)) := by ac_rfl
        _ = _ := by rw [hcancel, mul_one]
    _ = ENNReal.ofReal (C * t ^ (-(γ + p))) := by
      rw [hk, ← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg ht.le _))]
      congr 1
      rw [show -(γ + p) = -γ + -p by ring, Real.rpow_add ht]
      ring

theorem lag_energy_of_power_bound {a : ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    {C p γ : ℝ} (ha : a ≠ 0) (hatop : a ≠ ⊤) (hC : 0 ≤ C)
    (hexponent : γ + p < 1)
    (hq : ∀ t ∈ Ioo (0 : ℝ) 1,
      q t ≤ ENNReal.ofReal C * a ^ 2 * ENNReal.ofReal (t ^ (-p))) :
    (∫⁻ t in Ioc (0 : ℝ) 1, frostmanKernel γ 0 t * a⁻¹ ^ 2 * q t) ≤
      ENNReal.ofReal (C / (1 - (γ + p))) := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-(γ + p))) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)).const_mul C
  calc
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (C * t ^ (-(γ + p))) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t ht
      exact normalized_pointwise_bound ha hatop hC ht.1 (hq t ht)
    _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, C * t ^ (-(γ + p))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hint
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg hC (Real.rpow_nonneg ht.1.le _)
    _ = _ := by
      rw [integral_const_mul, power_integral_unit hexponent]
      congr 1
      ring

theorem uniform_lag_energy_below_thirty_one_over_thirty_six
    {ι : Type*} {a : ι → ℝ≥0∞} {q : ι → ℝ → ℝ≥0∞} {γ : ℝ}
    (ha : ∀ i, a i ≠ 0) (hatop : ∀ i, a i ≠ ⊤)
    (hγ : γ < 31 / 36)
    (hradial : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1,
        q i t ≤ ENNReal.ofReal C * (a i) ^ 2 *
          ENNReal.ofReal (t ^ (-(5 / 36 + δ)))) :
    ∃ B : ℝ, 0 < B ∧ ∀ i,
      (∫⁻ t in Ioc (0 : ℝ) 1, frostmanKernel γ 0 t * (a i)⁻¹ ^ 2 * q i t) ≤
        ENNReal.ofReal B := by
  obtain ⟨δ, hδ, he⟩ := exists_radial_exponent_loss hγ
  obtain ⟨C, hC, hbound⟩ := hradial δ hδ
  refine ⟨C / (1 - (γ + (5 / 36 + δ))) + 1, ?_, ?_⟩
  · have := div_nonneg hC (by linarith : 0 ≤ 1 - (γ + (5 / 36 + δ)))
    linarith
  · intro i
    apply (lag_energy_of_power_bound (ha i) (hatop i) hC he (hbound i)).trans
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- A countable family of strict rational lower bounds attains its endpoint.
This avoids taking an uncountable intersection of probability-one events. -/
theorem ae_endpoint_of_rational_lower_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ≥0∞) {d : ℝ} (hd : 0 < d)
    (h : ∀ q : ℚ, 0 < q → (q : ℝ) < d →
      ∀ᵐ ω ∂μ, ENNReal.ofReal (q : ℝ) ≤ D ω) :
    ∀ᵐ ω ∂μ, ENNReal.ofReal d ≤ D ω := by
  have hall : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 < q → (q : ℝ) < d →
      ENNReal.ofReal (q : ℝ) ≤ D ω := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < q ∧ (q : ℝ) < d
    · exact (h q hq.1 hq.2).mono (fun _ hw _ _ => hw)
    · exact Filter.Eventually.of_forall (fun _ hp hlt => (hq ⟨hp, hlt⟩).elim)
  filter_upwards [hall] with ω hω
  by_contra hn
  have hlt : D ω < ENNReal.ofReal d := lt_of_not_ge hn
  have hfinite : D ω ≠ ⊤ := ne_top_of_lt hlt
  have hreal : (D ω).toReal < d := by
    have ht := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hlt
    simpa only [ENNReal.toReal_ofReal hd.le] using ht
  obtain ⟨q, hqD, hqd⟩ := exists_rat_btwn hreal
  have hqpos : 0 < q := by
    exact_mod_cast (ENNReal.toReal_nonneg.trans_lt hqD)
  have hqle := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp (hω q hqpos hqd)
  exact (not_lt_of_ge hqle) hqD

/-- The endpoint 31/36 follows for the actual exceptional set in the unit
window from the displayed new radial bound and the stated process properties.
This is a reduction, not a proof that those properties or that bound hold
for any exchange process. -/
theorem ae_unit_lowerDimension_of_radial_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (v : Site) (a : ℕ → ℝ≥0∞) (ha : ∀ R, a R ≠ 0) (hatop : ∀ R, a R ≠ ⊤)
    (hmarginal : ∀ R t, μ {ω | OneArm (X ω t) v R} = a R)
    (hstationary : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      μ {ω | OneArm (X ω s) v R ∧ OneArm (X ω t) v R} =
        μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω (dist s t)) v R})
    (hradial : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ R, ∀ t ∈ Ioo (0 : ℝ) 1,
        μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω t) v R} ≤
          ENNReal.ofReal C * (a R) ^ 2 * ENNReal.ofReal (t ^ (-(5 / 36 + δ))))
    (hpreserve : ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (X ω) v)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
    (hshift : Function.Semiconj X e (translateTrajectory z)) :
    ∀ᵐ ω ∂μ, (31 / 36 : ℝ≥0∞) ≤ dimH (exceptionalTimes (X ω) ∩ Icc 0 1) := by
  have h := ae_endpoint_of_rational_lower_bounds μ
    (fun ω => dimH (exceptionalTimes (X ω) ∩ Icc 0 1))
    (by norm_num : (0 : ℝ) < 31 / 36) ?_
  · have heq : ENNReal.ofReal (31 / 36 : ℝ) = (31 / 36 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 36)]
      norm_num
    simpa only [heq] using h
  · intro q hq hqd
    obtain ⟨B, hB, hbound⟩ :=
      uniform_lag_energy_below_thirty_one_over_thirty_six ha hatop hqd hradial
    apply OccupationWitnesses.ae_unit_lowerDimension_of_lag_bound hcapacity μ X hX
      v a ha hatop hmarginal hstationary (by exact_mod_cast hq) hB hbound
      hpreserve e he z hshift

end ExceptionalTimes.CorrelationPowerBound

#print axioms ExceptionalTimes.CorrelationPowerBound.lag_energy_of_power_bound
#print axioms ExceptionalTimes.CorrelationPowerBound.uniform_lag_energy_below_thirty_one_over_thirty_six
#print axioms ExceptionalTimes.CorrelationPowerBound.ae_unit_lowerDimension_of_radial_bound

