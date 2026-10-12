import ExceptionalTimes.Model
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
The nonnegative extended energy needed at the weak-limit/Frostman step.
For a positive exponent its diagonal is infinity. Using a real negative
power first and only then converting to ENNReal would set the diagonal
to zero and would incorrectly permit atoms in a finite-energy measure.

The compactness/capacity theorem is not asserted in this file.
-/

namespace ExceptionalTimes

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

noncomputable def frostmanKernel (γ : ℝ) (s t : ℝ) : ℝ≥0∞ :=
  (edist s t) ^ (-γ)

noncomputable def frostmanPotential (γ : ℝ) (μ : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, frostmanKernel γ s t ∂μ

noncomputable def frostmanEnergy (γ : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s, frostmanPotential γ μ s ∂μ

theorem frostmanKernel_diagonal {γ : ℝ} (hγ : 0 < γ) (s : ℝ) :
    frostmanKernel γ s s = ⊤ := by
  simp only [frostmanKernel, edist_self]
  exact ENNReal.zero_rpow_of_neg (neg_neg_of_pos hγ)

theorem frostmanKernel_off_diagonal (γ : ℝ) {s t : ℝ} (hst : s ≠ t) :
    frostmanKernel γ s t = ENNReal.ofReal ((dist s t) ^ (-γ)) := by
  rw [frostmanKernel, edist_dist,
    ENNReal.ofReal_rpow_of_pos (dist_pos.mpr hst)]

theorem frostmanPotential_top_of_atom {γ : ℝ} (hγ : 0 < γ) (μ : Measure ℝ)
    (s : ℝ) (hs : μ {s} ≠ 0) : frostmanPotential γ μ s = ⊤ := by
  have h := setLIntegral_le_lintegral (μ := μ) {s} (frostmanKernel γ s)
  rw [lintegral_singleton, frostmanKernel_diagonal hγ, ENNReal.top_mul hs] at h
  exact top_unique h

theorem frostmanEnergy_top_of_atom {γ : ℝ} (hγ : 0 < γ) (μ : Measure ℝ)
    (s : ℝ) (hs : μ {s} ≠ 0) : frostmanEnergy γ μ = ⊤ := by
  have h := setLIntegral_le_lintegral (μ := μ) {s} (frostmanPotential γ μ)
  rw [lintegral_singleton, frostmanPotential_top_of_atom hγ μ s hs,
    ENNReal.top_mul hs] at h
  exact top_unique h

theorem noAtoms_of_frostmanEnergy_lt_top {γ : ℝ} (hγ : 0 < γ) (μ : Measure ℝ)
    (hfinite : frostmanEnergy γ μ < ⊤) : NullSingletonClass μ := by
  constructor
  intro s
  by_contra hs
  exact hfinite.ne (frostmanEnergy_top_of_atom hγ μ s hs)

end ExceptionalTimes

#print axioms ExceptionalTimes.frostmanKernel_diagonal
#print axioms ExceptionalTimes.frostmanEnergy_top_of_atom
#print axioms ExceptionalTimes.noAtoms_of_frostmanEnergy_lt_top
