import ExceptionalTimes.CorrelationPowerBound

/-! Deterministic time-window transport. Positive affine changes preserve
Hausdorff dimension and the one-sided site-closure implication. -/

namespace ExceptionalTimes.AffineTimeWindows

open Set MeasureTheory
open scoped ENNReal

def affineTime (a c : ℝ) (X : Trajectory) : Trajectory := fun t => X (a + c * t)

theorem measurable_affineTime {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Trajectory} (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (a c : ℝ) : Measurable (fun p : Ω × ℝ => affineTime a c (X p.1) p.2) := by
  exact hX.comp (measurable_fst.prodMk
    (measurable_const.add (measurable_const.mul measurable_snd)))

theorem closure_preserves_affineTime {X : Trajectory} {v : Site}
    (hX : TimeClosure.SiteClosurePreservesInfiniteAt X v)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    TimeClosure.SiteClosurePreservesInfiniteAt (affineTime a c X) v := by
  intro t ht hblack
  apply hX (a + c * t) (add_nonneg ha (mul_nonneg hc ht))
  apply hblack.mono
  apply blackCluster_mono
  intro w hw
  rw [TimeClosure.closedColors_eq_true] at hw ⊢
  have hcont : Continuous (fun s : ℝ => a + c * s) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hmem := mem_closure_image hcont.continuousAt hw
  apply closure_mono _ hmem
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨add_nonneg ha (mul_nonneg hc hs.1), hs.2⟩

theorem percolation_closure_preserves_affineTime {X : Trajectory} {v : Site}
    (hX : TimeClosure.SiteClosurePreservesPercolationAt X v)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    TimeClosure.SiteClosurePreservesPercolationAt (affineTime a c X) v := by
  intro t ht hblack
  apply hX (a + c * t) (add_nonneg ha (mul_nonneg hc ht))
  apply hblack.mono
  apply blackCluster_mono
  intro w hw
  rw [TimeClosure.closedColors_eq_true] at hw ⊢
  have hcont : Continuous (fun s : ℝ => a + c * s) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hmem := mem_closure_image hcont.continuousAt hw
  apply closure_mono _ hmem
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨add_nonneg ha (mul_nonneg hc hs.1), hs.2⟩

theorem dimH_affine_image (a : ℝ) {c : ℝ} (hc : 0 < c) (S : Set ℝ) :
    dimH ((fun t : ℝ => a + c * t) '' S) = dimH S := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have htrans : Isometry (fun t : ℝ => a + t) :=
    Isometry.of_dist_eq (fun _ _ => dist_add_left _ _ _)
  have heq : ((fun t : ℝ => a + c * t) '' S) =
      (fun t : ℝ => a + t) '' (e '' S) := by
    rw [image_image]
    rfl
  rw [heq, htrans.dimH_image, e.dimH_image]

theorem exceptional_unit_image (X : Trajectory) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) :
    (fun t : ℝ => a + c * t) '' (exceptionalTimes (affineTime a c X) ∩ Icc 0 1) =
      exceptionalTimes X ∩ Icc a (a + c) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨add_nonneg ha (mul_nonneg hc.le hs.2.1), hs.1.2⟩, ?_, ?_⟩
    · exact le_add_of_nonneg_right (mul_nonneg hc.le hs.2.1)
    · nlinarith [hs.2.2]
  · intro ht
    refine ⟨(t - a) / c, ?_, ?_⟩
    · have hnonneg : 0 ≤ (t - a) / c := div_nonneg (sub_nonneg.mpr ht.2.1) hc.le
      have heq : a + c * ((t - a) / c) = t := by field_simp; ring
      refine ⟨⟨hnonneg, ?_⟩, hnonneg, ?_⟩
      · simpa only [affineTime, heq] using ht.1.2
      · apply (div_le_iff₀ hc).mpr
        linarith [ht.2.2]
    · field_simp
      ring

theorem dimH_exceptional_affine_unit (X : Trajectory) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 < c) :
    dimH (exceptionalTimes (affineTime a c X) ∩ Icc 0 1) =
      dimH (exceptionalTimes X ∩ Icc a (a + c)) := by
  rw [← exceptional_unit_image X ha hc, dimH_affine_image a hc]

end ExceptionalTimes.AffineTimeWindows

#print axioms ExceptionalTimes.AffineTimeWindows.closure_preserves_affineTime
#print axioms ExceptionalTimes.AffineTimeWindows.dimH_exceptional_affine_unit

