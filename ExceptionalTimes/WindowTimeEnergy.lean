import ExceptionalTimes.OccupationMoments
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Convert a stationary time-lag energy bound to a double-time occupation
energy bound on [0,1]. The nonnegative integrands may take the value infinity.
In particular no value at the diagonal is changed for this argument. -/

namespace ExceptionalTimes.WindowTimeEnergy

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem negative_interval_reflection (h : ℝ → ℝ≥0∞) :
    (∫⁻ u in Icc (-1 : ℝ) 0, h |u|) = ∫⁻ u in Icc (0 : ℝ) 1, h u := by
  rw [← lintegral_indicator measurableSet_Icc]
  rw [← lintegral_neg_eq_self (μ := volume)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro u
  have he : -u ∈ Icc (-1 : ℝ) 0 ↔ u ∈ Icc (0 : ℝ) 1 := by
    simp only [mem_Icc]
    constructor <;> intro hu <;> constructor <;> linarith [hu.1, hu.2]
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · simp [he.mpr hu, hu, abs_neg, abs_of_nonneg hu.1]
  · simp [hu, mt he.mp hu]

theorem symmetric_interval_le_two (h : ℝ → ℝ≥0∞) :
    (∫⁻ u in Icc (-1 : ℝ) 1, h |u|) ≤ 2 * ∫⁻ u in Icc (0 : ℝ) 1, h u := by
  have hs : Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 0 ∪ Icc (0 : ℝ) 1 := by
    ext u
    simp only [mem_Icc, mem_union]
    constructor
    · intro hu
      rcases le_total u 0 with h | h
      · exact Or.inl ⟨hu.1, h⟩
      · exact Or.inr ⟨h, hu.2⟩
    · rintro (hu | hu) <;> constructor <;> linarith [hu.1, hu.2]
  rw [hs]
  refine (lintegral_union_le _ _ _).trans ?_
  rw [negative_interval_reflection]
  have hp : (∫⁻ u in Icc (0 : ℝ) 1, h |u|) = ∫⁻ u in Icc (0 : ℝ) 1, h u :=
    setLIntegral_congr_fun measurableSet_Icc (fun u hu => by rw [abs_of_nonneg hu.1])
  rw [hp, two_mul]

theorem interval_lag_le (h : ℝ → ℝ≥0∞) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫⁻ t in Icc (0 : ℝ) 1, h (dist s t)) ≤
      2 * ∫⁻ u in Icc (0 : ℝ) 1, h u := by
  let g : ℝ → ℝ≥0∞ := (Icc (-1 : ℝ) 1).indicator (fun u => h |u|)
  calc
    _ = ∫⁻ t, (Icc (0 : ℝ) 1).indicator (fun t => h (dist s t)) t :=
      (lintegral_indicator measurableSet_Icc _).symm
    _ ≤ ∫⁻ t, g (t - s) := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ Icc (0 : ℝ) 1
      · have hb : t - s ∈ Icc (-1 : ℝ) 1 := by
          constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
        simp only [g, indicator_of_mem ht, indicator_of_mem hb]
        rw [Real.dist_eq, abs_sub_comm]
      · simp [ht]
    _ = ∫⁻ u, g u := lintegral_sub_right_eq_self g s
    _ = ∫⁻ u in Icc (-1 : ℝ) 1, h |u| := lintegral_indicator measurableSet_Icc _
    _ ≤ _ := symmetric_interval_le_two h

theorem double_interval_lag_le (h : ℝ → ℝ≥0∞) :
    (∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ t in Icc (0 : ℝ) 1, h (dist s t)) ≤
      2 * ∫⁻ u in Ioc (0 : ℝ) 1, h u := by
  rw [restrict_Ioc_eq_restrict_Icc]
  calc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, 2 * ∫⁻ u in Icc (0 : ℝ) 1, h u :=
      setLIntegral_mono' measurableSet_Icc (fun s hs => interval_lag_le h hs)
    _ = _ := by simp

theorem frostmanKernel_lag (γ s t : ℝ) :
    frostmanKernel γ s t = frostmanKernel γ 0 (dist s t) := by
  unfold frostmanKernel
  rw [edist_dist, edist_dist, Real.dist_eq (0 : ℝ), zero_sub, abs_neg,
    abs_of_nonneg dist_nonneg]

/-- Joint stationarity is needed only through the displayed two-time identity.
The time-lag bound itself remains an explicit percolation obligation. -/
theorem twoTime_energy_le_lag_energy (q : ℝ → ℝ≥0∞) (Q : ℝ → ℝ → ℝ≥0∞)
    (hQ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Q s t = q (dist s t))
    (γ : ℝ) (c : ℝ≥0∞) :
    (∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ t in Icc (0 : ℝ) 1,
      frostmanKernel γ s t * c ^ 2 * Q s t) ≤
      2 * ∫⁻ u in Ioc (0 : ℝ) 1, frostmanKernel γ 0 u * c ^ 2 * q u := by
  have heq : (∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ t in Icc (0 : ℝ) 1,
      frostmanKernel γ s t * c ^ 2 * Q s t) =
      ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ t in Icc (0 : ℝ) 1,
        frostmanKernel γ 0 (dist s t) * c ^ 2 * q (dist s t) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hQ s hs t ht, frostmanKernel_lag]
  rw [heq]
  exact double_interval_lag_le (fun u => frostmanKernel γ 0 u * c ^ 2 * q u)

end ExceptionalTimes.WindowTimeEnergy

#print axioms ExceptionalTimes.WindowTimeEnergy.double_interval_lag_le
#print axioms ExceptionalTimes.WindowTimeEnergy.twoTime_energy_le_lag_energy
