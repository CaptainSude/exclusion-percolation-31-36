import ExceptionalTimes.WindowDimensionReduction
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace ExceptionalTimes.LagScaling

open MeasureTheory Set
open scoped ENNReal

theorem lintegral_mul_left (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    (∫⁻ t, f (c * t)) = ENNReal.ofReal c⁻¹ * ∫⁻ u, f u := by
  let e := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hc.ne').unit : ℝ ≃ₜ ℝ).toMeasurableEquiv
  have he : (e : ℝ → ℝ) = fun t => c * t := by
    funext t
    change (isUnit_iff_ne_zero.mpr hc.ne').unit • t = c * t
    simp only [Units.smul_def, IsUnit.unit_spec, smul_eq_mul]
  have hm : Measure.map e volume = ENNReal.ofReal c⁻¹ • (volume : Measure ℝ) := by
    rw [he]
    have h := Measure.map_addHaar_smul (volume : Measure ℝ) hc.ne'
    simpa [abs_of_pos (inv_pos.mpr hc)] using h
  have h := lintegral_map_equiv (μ := volume) f e
  rw [hm, lintegral_smul_measure] at h
  simpa only [he, smul_eq_mul] using h.symm

theorem setLIntegral_mul_unit (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    (∫⁻ t in Ioc (0 : ℝ) 1, f (c * t)) =
      ENNReal.ofReal c⁻¹ * ∫⁻ u in Ioc (0 : ℝ) c, f u := by
  rw [← lintegral_indicator measurableSet_Ioc]
  have he : (fun t => (Ioc (0 : ℝ) 1).indicator (fun t => f (c * t)) t) =
      fun t => (Ioc (0 : ℝ) c).indicator f (c * t) := by
    funext t
    have ht : c * t ∈ Ioc (0 : ℝ) c ↔ t ∈ Ioc (0 : ℝ) 1 := by
      change (0 < c * t ∧ c * t ≤ c) ↔ (0 < t ∧ t ≤ 1)
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨(mul_pos_iff_of_pos_left hc).mp h0,
          (mul_le_mul_iff_right₀ hc).mp (by simpa using h1)⟩
      · rintro ⟨h0, h1⟩
        exact ⟨mul_pos hc h0, by simpa using mul_le_mul_of_nonneg_left h1 hc.le⟩
    by_cases h : t ∈ Ioc (0 : ℝ) 1
    · simp [h, ht.mpr h]
    · simp [h, mt ht.mp h]
  rw [he, lintegral_mul_left _ hc, lintegral_indicator measurableSet_Ioc]

theorem frostmanKernel_scale (γ : ℝ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    frostmanKernel γ 0 t = ENNReal.ofReal (c ^ γ) * frostmanKernel γ 0 (c * t) := by
  rw [frostmanKernel_off_diagonal γ (ne_of_lt ht),
    frostmanKernel_off_diagonal γ (ne_of_lt (mul_pos hc ht)),
    Real.dist_eq, Real.dist_eq, zero_sub, zero_sub, abs_neg, abs_neg,
    abs_of_pos ht, abs_of_pos (mul_pos hc ht),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  congr 1
  rw [Real.mul_rpow hc.le ht.le, ← mul_assoc, ← Real.rpow_add hc]
  simp

/-- Rescaling time preserves a finite lag-energy bound. The diagonal is
excluded by the interval, rather than assigning it an incorrect finite value. -/
theorem lag_energy_scale_le (q : ℝ → ℝ≥0∞) (a : ℝ≥0∞) (γ : ℝ)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫⁻ t in Ioc (0 : ℝ) 1, frostmanKernel γ 0 t * a * q (c * t)) ≤
      (ENNReal.ofReal (c ^ γ) * ENNReal.ofReal c⁻¹) *
        ∫⁻ u in Ioc (0 : ℝ) 1, frostmanKernel γ 0 u * a * q u := by
  calc
    _ = ∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (c ^ γ) * (frostmanKernel γ 0 (c * t) * a * q (c * t)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [frostmanKernel_scale γ hc ht.1]
      ac_rfl
    _ = ENNReal.ofReal (c ^ γ) *
        ∫⁻ t in Ioc (0 : ℝ) 1, frostmanKernel γ 0 (c * t) * a * q (c * t) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = (ENNReal.ofReal (c ^ γ) * ENNReal.ofReal c⁻¹) *
        ∫⁻ u in Ioc (0 : ℝ) c, frostmanKernel γ 0 u * a * q u := by
      rw [setLIntegral_mul_unit (fun u => frostmanKernel γ 0 u * a * q u) hc, mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set (Ioc_subset_Ioc le_rfl hc1))

section Dimension

open AffineTimeWindows WindowDimensionReduction

variable {Ω : Type*} [MeasurableSpace Ω]
variable (hcapacity : PublishedCapacity.SchrammSteifCapacity)
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
variable (v : Site) (α : ℕ → ℝ≥0∞)
variable (hα : ∀ R, α R ≠ 0) (hαtop : ∀ R, α R ≠ ⊤)
variable (hmarginal : ∀ R t, μ {ω | OneArm (X ω t) v R} = α R)
variable (hstationary : ∀ R s t, 0 ≤ s → 0 ≤ t →
  μ {ω | OneArm (X ω s) v R ∧ OneArm (X ω t) v R} =
    μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω (dist s t)) v R})
variable (henergy : ∀ γ : ℝ, 0 < γ → γ < 31 / 36 → ∃ B : ℝ, 0 < B ∧ ∀ R,
  (∫⁻ t in Ioc (0 : ℝ) 1, frostmanKernel γ 0 t * (α R)⁻¹ ^ 2 *
    μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω t) v R}) ≤ ENNReal.ofReal B)
variable (hpreserve : ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (X ω) v)
variable (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
variable (hshift : Function.Semiconj X e (translateTrajectory z))

include hcapacity hX hα hαtop hmarginal hstationary henergy hpreserve he hshift in
theorem ae_lowerDimension_short_window_of_energy
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᵐ ω ∂μ, (31 / 36 : ℝ≥0∞) ≤
      dimH (exceptionalTimes (X ω) ∩ Icc a (a + c)) := by
  have hendpoint := CorrelationPowerBound.ae_endpoint_of_rational_lower_bounds μ
    (fun ω => dimH (exceptionalTimes (X ω) ∩ Icc a (a + c)))
    (by norm_num : (0 : ℝ) < 31 / 36) ?_
  · have heq : ENNReal.ofReal (31 / 36 : ℝ) = (31 / 36 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 36)]
      norm_num
    simpa only [heq] using hendpoint
  · intro q hq hqd
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    obtain ⟨B, hB, hbound⟩ := henergy q hqpos hqd
    let B' : ℝ := c ^ (q : ℝ) * c⁻¹ * B
    have hB' : 0 < B' := mul_pos (mul_pos (Real.rpow_pos_of_pos hc _) (inv_pos.mpr hc)) hB
    have hd : ∀ s t : ℝ,
        dist (a + c * s) (a + c * t) = dist a (a + c * dist s t) := by
      intro s t
      rw [affine_dist a s t hc]
      have h := affine_dist a 0 (dist s t) hc
      simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg (x := s) (y := t))] using h.symm
    have hlow := OccupationWitnesses.ae_unit_lowerDimension_of_lag_bound hcapacity μ
      (fun ω => affineTime a c (X ω)) (measurable_affineTime hX a c) v α hα hαtop
      (fun R t => hmarginal R (a + c * t)) ?_ hqpos hB' ?_ ?_ e he z ?_
    · exact hlow.mono fun ω hω => by
        rwa [dimH_exceptional_affine_unit (X ω) ha hc] at hω
    · intro R s hs t ht
      change μ {ω | OneArm (X ω (a + c * s)) v R ∧ OneArm (X ω (a + c * t)) v R} =
        μ {ω | OneArm (X ω (a + c * 0)) v R ∧ OneArm (X ω (a + c * dist s t)) v R}
      rw [mul_zero, add_zero,
        hstationary R _ _ (add_nonneg ha (mul_nonneg hc.le hs.1))
          (add_nonneg ha (mul_nonneg hc.le ht.1)),
        hstationary R _ _ ha (add_nonneg ha (mul_nonneg hc.le dist_nonneg)), hd s t]
    · intro R
      have heq : (∫⁻ t in Ioc (0 : ℝ) 1, frostmanKernel (q : ℝ) 0 t * (α R)⁻¹ ^ 2 *
          μ {ω | OneArm (affineTime a c (X ω) 0) v R ∧
            OneArm (affineTime a c (X ω) t) v R}) =
          ∫⁻ t in Ioc (0 : ℝ) 1, frostmanKernel (q : ℝ) 0 t * (α R)⁻¹ ^ 2 *
            μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω (c * t)) v R} := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        dsimp only [affineTime]
        rw [mul_zero, add_zero, hstationary R _ _ ha
          (add_nonneg ha (mul_nonneg hc.le ht.1.le))]
        have hdist : dist a (a + c * t) = c * t := by
          simpa only [mul_zero, add_zero, Real.dist_eq, zero_sub, abs_neg, abs_of_pos ht.1]
            using affine_dist a 0 t hc
        rw [hdist]
      rw [heq]
      apply (lag_energy_scale_le
        (fun t => μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω t) v R})
        ((α R)⁻¹ ^ 2) q hc hc1).trans
      apply (mul_le_mul' le_rfl (hbound R)).trans_eq
      simp only [B', ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
        ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hc.le _) (inv_nonneg.mpr hc.le))]
    · exact hpreserve.mono fun _ hω => percolation_closure_preserves_affineTime hω ha hc.le
    · intro ω
      funext t w
      exact congrFun (congrFun (hshift ω) (a + c * t)) w

include hcapacity hX hα hαtop hmarginal hstationary henergy hpreserve he hshift in
/-- This is the dimension driver appropriate for spectral comparison: it
requires integrated correlations, not a stronger pointwise radial estimate.
The energy bound is a new obligation until proved for the stated process. -/
theorem almostSureConjecturedDimension_of_lag_energy
    (hupper : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (X ω)) ≤ (31 / 36 : ℝ≥0∞)) :
    AlmostSureConjecturedDimension μ X := by
  apply ae_exceptionalDimension_of_ae_rational_windows μ X (31 / 36)
  intro p q hp hpq
  have ha : (0 : ℝ) ≤ p := by exact_mod_cast hp
  have hab : (p : ℝ) < q := by exact_mod_cast hpq
  let c : ℝ := min (((q : ℝ) - p) / 3) (1 / 3)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hcsize : c ≤ ((q : ℝ) - p) / 3 := min_le_left _ _
  have hlow := ae_lowerDimension_short_window_of_energy hcapacity μ X hX v α hα hαtop
    hmarginal hstationary henergy hpreserve e he z hshift
    (add_nonneg ha hc.le) hc hc1
  filter_upwards [hlow, hupper] with ω hl hu
  apply le_antisymm ((dimH_mono inter_subset_left).trans hu)
  exact hl.trans (dimH_mono (by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2.1], by linarith [ht.2.2]⟩))

end Dimension
end ExceptionalTimes.LagScaling

#print axioms ExceptionalTimes.LagScaling.lag_energy_scale_le
#print axioms ExceptionalTimes.LagScaling.almostSureConjecturedDimension_of_lag_energy

