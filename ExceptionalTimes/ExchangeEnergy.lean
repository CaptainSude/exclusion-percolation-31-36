import ExceptionalTimes.Model
import ExceptionalTimes.KernelMatching
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
The actual configuration swap and its nonnegative exchange energy.
The sum is over ordered pairs, so its factor is one quarter: each
unordered edge is counted twice, and the jump energy has factor one half.

Extended nonnegative integrals and sums allow the comparison to be proved
without an artificial finite-volume or summability assumption on the test
function. Identifying this expression with a closed Markov Dirichlet form
is a separate analytic obligation.
-/

namespace ExceptionalTimes

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

/-- Exchange the colors at two actual sites of the infinite lattice. -/
noncomputable def swapColors (x y : Site) (ω : Configuration) : Configuration :=
  ω ∘ Equiv.swap x y

theorem swapColors_involutive (x y : Site) :
    Function.Involutive (swapColors x y) := by
  intro ω
  funext v
  simp [swapColors]

theorem swapColors_diagonal (x : Site) (ω : Configuration) : swapColors x x ω = ω := by
  funext v
  simp [swapColors]

theorem swapColors_symmetric (x y : Site) (ω : Configuration) :
    swapColors x y ω = swapColors y x ω := by
  simp only [swapColors, Equiv.swap_comm]

/-- Squared jump of a real observable, integrated under a configuration law. -/
noncomputable def swapEnergy (μ : Measure Configuration) (f : Configuration → ℝ)
    (x y : Site) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((f (swapColors x y ω) - f ω) ^ 2) ∂μ

/-- The extended quadratic exchange energy, with ordered-pair convention. -/
noncomputable def exchangeEnergy (μ : Measure Configuration) (f : Configuration → ℝ)
    (rate : Site → Site → ℝ) : ℝ≥0∞ :=
  (1 / 4 : ℝ≥0∞) * ∑' p : Site × Site,
    ENNReal.ofReal (rate p.1 p.2) * swapEnergy μ f p.1 p.2

theorem swapEnergy_symmetric (μ : Measure Configuration) (f : Configuration → ℝ)
    (x y : Site) : swapEnergy μ f x y = swapEnergy μ f y x := by
  simp only [swapEnergy, swapColors_symmetric x y]

theorem swapEnergy_diagonal (μ : Measure Configuration) (f : Configuration → ℝ)
    (x : Site) : swapEnergy μ f x x = 0 := by
  simp [swapEnergy, swapColors_diagonal]

/-- Pointwise domination of nonnegative rates gives energy domination. -/
theorem exchangeEnergy_mono (μ : Measure Configuration) (f : Configuration → ℝ)
    {r s : Site → Site → ℝ} (hrs : ∀ x y, r x y ≤ s x y) :
    exchangeEnergy μ f r ≤ exchangeEnergy μ f s := by
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro p
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hrs p.1 p.2)) _

theorem exchangeEnergy_scale (μ : Measure Configuration) (f : Configuration → ℝ)
    (r : Site → Site → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    exchangeEnergy μ f (fun x y => c * r x y) =
      ENNReal.ofReal c * exchangeEnergy μ f r := by
  simp only [exchangeEnergy, ENNReal.ofReal_mul hc, mul_assoc]
  rw [ENNReal.tsum_mul_left]
  ac_rfl

/-- The comparison is for the concrete infinite sum of squared color swaps.
It permits infinite energy and does not assert a semigroup comparison. -/
theorem matching_exchangeEnergy_domination (k : RateKernel)
    (μ : Measure Configuration) (f : Configuration → ℝ) (z : Site) :
    ENNReal.ofReal (2 * k.rate z) *
        exchangeEnergy μ f (canonicalMatchingRate z) ≤
      exchangeEnergy μ f k.pairRate := by
  rw [← exchangeEnergy_scale μ f _ (mul_nonneg (by norm_num) (k.nonneg z))]
  exact exchangeEnergy_mono μ f (matching_rate_domination k z)

theorem exists_matching_energy_comparison (k : RateKernel) :
    ∃ z : Site, z ≠ 0 ∧ 0 < k.rate z ∧
      ∀ (μ : Measure Configuration) (f : Configuration → ℝ),
        ENNReal.ofReal (2 * k.rate z) *
            exchangeEnergy μ f (canonicalMatchingRate z) ≤
          exchangeEnergy μ f k.pairRate := by
  obtain ⟨z, hz, hpos⟩ := k.exists_positive_displacement
  exact ⟨z, hz, hpos, fun μ f => matching_exchangeEnergy_domination k μ f z⟩

end ExceptionalTimes

#print axioms ExceptionalTimes.swapColors_involutive
#print axioms ExceptionalTimes.exchangeEnergy_mono
#print axioms ExceptionalTimes.matching_exchangeEnergy_domination
#print axioms ExceptionalTimes.exists_matching_energy_comparison
