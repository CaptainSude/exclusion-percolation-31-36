import ExceptionalTimes.AffineTimeWindows

/-! A complete dimension reduction for a concrete trajectory-valued random
variable, conditional on the NEW radial estimate and explicit process laws.
This file does not establish the radial estimate for exclusion dynamics and
is not the requested theorem conditional only on published results. -/

namespace ExceptionalTimes.WindowDimensionReduction

open Set MeasureTheory AffineTimeWindows
open scoped ENNReal

theorem affine_dist (a s t : ℝ) {c : ℝ} (hc : 0 < c) :
    dist (a + c * s) (a + c * t) = c * dist s t := by
  simp only [Real.dist_eq]
  rw [show a + c * s - (a + c * t) = c * (s - t) by ring,
    abs_mul, abs_of_pos hc]

section Reduction

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
variable (hradial : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
  ∀ R, ∀ t ∈ Ioo (0 : ℝ) 1,
    μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω t) v R} ≤
      ENNReal.ofReal C * (α R) ^ 2 * ENNReal.ofReal (t ^ (-(5 / 36 + δ))))
variable (hpreserve : ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (X ω) v)
variable (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
variable (hshift : Function.Semiconj X e (translateTrajectory z))

include hcapacity hX hα hαtop hmarginal hstationary hradial hpreserve he hshift in
theorem ae_lowerDimension_short_closed_window
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᵐ ω ∂μ, (31 / 36 : ℝ≥0∞) ≤
      dimH (exceptionalTimes (X ω) ∩ Icc a (a + c)) := by
  have hd : ∀ s t : ℝ,
      dist (a + c * s) (a + c * t) = dist a (a + c * dist s t) := by
    intro s t
    rw [affine_dist a s t hc]
    have h := affine_dist a 0 (dist s t) hc
    simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg (x := s) (y := t))] using h.symm
  have hlow := CorrelationPowerBound.ae_unit_lowerDimension_of_radial_bound hcapacity μ
    (fun ω => affineTime a c (X ω)) (measurable_affineTime hX a c) v α hα hαtop
    (fun R t => hmarginal R (a + c * t)) ?_ ?_ ?_ e he z ?_
  · exact hlow.mono fun ω hω => by
      rwa [dimH_exceptional_affine_unit (X ω) ha hc] at hω
  · intro R s hs t ht
    change μ {ω | OneArm (X ω (a + c * s)) v R ∧ OneArm (X ω (a + c * t)) v R} =
      μ {ω | OneArm (X ω (a + c * 0)) v R ∧ OneArm (X ω (a + c * dist s t)) v R}
    rw [mul_zero, add_zero,
      hstationary R _ _ (add_nonneg ha (mul_nonneg hc.le hs.1))
        (add_nonneg ha (mul_nonneg hc.le ht.1)),
      hstationary R _ _ ha (add_nonneg ha (mul_nonneg hc.le dist_nonneg)), hd s t]
  · intro δ hδ
    obtain ⟨C, hC, hbound⟩ := hradial δ hδ
    refine ⟨C * c ^ (-(5 / 36 + δ)), by positivity, ?_⟩
    intro R t ht
    change μ {ω | OneArm (X ω (a + c * 0)) v R ∧ OneArm (X ω (a + c * t)) v R} ≤ _
    rw [mul_zero, add_zero, hstationary R _ _ ha
      (add_nonneg ha (mul_nonneg hc.le ht.1.le))]
    have hdist : dist a (a + c * t) = c * t := by
      simpa only [mul_zero, add_zero, Real.dist_eq, zero_sub, abs_neg, abs_of_pos ht.1]
        using affine_dist a 0 t hc
    rw [hdist]
    have hct : c * t ∈ Ioo (0 : ℝ) 1 :=
      ⟨mul_pos hc ht.1, lt_of_lt_of_le (mul_lt_mul_of_pos_left ht.2 hc) (by simpa using hc1)⟩
    apply (hbound R (c * t) hct).trans_eq
    rw [Real.mul_rpow hc.le ht.1.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ENNReal.ofReal_mul hC]
    ac_rfl
  · exact hpreserve.mono fun _ hω => percolation_closure_preserves_affineTime hω ha hc.le
  · intro ω
    funext t w
    exact congrFun (congrFun (hshift ω) (a + c * t)) w

include hcapacity hX hα hαtop hmarginal hstationary hradial hpreserve he hshift in
theorem ae_lowerDimension_open_window
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᵐ ω ∂μ, (31 / 36 : ℝ≥0∞) ≤ dimH (exceptionalTimes (X ω) ∩ Ioo a b) := by
  let c : ℝ := min ((b - a) / 3) (1 / 3)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hcsize : c ≤ (b - a) / 3 := min_le_left _ _
  have hsmall := ae_lowerDimension_short_closed_window hcapacity μ X hX v α hα hαtop
    hmarginal hstationary hradial hpreserve e he z hshift
    (add_nonneg ha hc.le) hc hc1
  exact hsmall.mono fun ω hω => hω.trans (dimH_mono (by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2.1], by linarith [ht.2.2]⟩))

include hcapacity hX hα hαtop hmarginal hstationary hradial hpreserve he hshift in
/-- Exact all-window dimension, with the missing radial theorem explicitly
displayed as `hradial`. The upper bound is also explicit, allowing a faithful
application of the published GV upper-bound theorem after model matching. -/
theorem almostSureConjecturedDimension_of_radial_bound
    (hupper : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (X ω)) ≤ (31 / 36 : ℝ≥0∞)) :
    AlmostSureConjecturedDimension μ X := by
  apply ae_exceptionalDimension_of_ae_rational_windows μ X (31 / 36)
  intro p q hp hpq
  have hlow := ae_lowerDimension_open_window hcapacity μ X hX v α hα hαtop
    hmarginal hstationary hradial hpreserve e he z hshift
    (by exact_mod_cast hp : (0 : ℝ) ≤ p) (by exact_mod_cast hpq : (p : ℝ) < q)
  filter_upwards [hlow, hupper] with ω hl hu
  exact le_antisymm ((dimH_mono inter_subset_left).trans hu) hl

end Reduction
end ExceptionalTimes.WindowDimensionReduction

#print axioms ExceptionalTimes.WindowDimensionReduction.almostSureConjecturedDimension_of_radial_bound

