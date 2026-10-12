import ExceptionalTimes.FiniteMatchingExhaustion
import ExceptionalTimes.KernelMatching

/-! Literal time normalization for an arbitrary nonzero summable rate kernel.
The canonical matching has swap rate one-half, so its clock unit is exactly
the reciprocal of twice the chosen positive displacement rate. -/

open MeasureTheory Set Filter
open scoped ENNReal Classical

namespace ExceptionalTimes.FiniteMatchingNormalization

open FiniteMatchingExhaustion

theorem unorderedPairRate_nonneg (k : RateKernel) (e : Sym2 Site) :
    0 ≤ k.unorderedPairRate e := by
  induction e using Sym2.inductionOn with
  | _ u v => exact k.pairRate_nonneg u v

theorem matching_normalization (k : RateKernel) (z : Site) (hz : 0 < k.rate z) (x : Site) :
    (1 / (2 * k.rate z)) * k.unorderedPairRate s(x, PeriodicMatching.partner z x) = 1 / 2 := by
  rw [RateKernel.unorderedPairRate_mk, partner_exchange_rate]
  field_simp [ne_of_gt hz]

theorem finite_energy_of_canonical_matching
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    (k : RateKernel) (P : PoissonGraphicalRealization μ k.unorderedPairRate)
    (z : Site) (hz : z ≠ (0, 0)) (hpos : 0 < k.rate z)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (v : Site) (hv : ∀ R, v ∈ latticeBox R) (α : ℕ → ℝ≥0∞)
    (hcanonical : CanonicalOneArmEnergyBound z v α) :
    ∀ γ : ℝ, 0 < γ → γ < 31 / 36 → ∃ B : ℝ, 0 < B ∧ ∀ R, ∀ᶠ n in atTop,
      (P.speedup (1 / (2 * k.rate z)) (by positivity)).truncatedCorrelationEnergy
        (F n) (fun η => OneArm η v R) γ
        (volume.restrict (Ioc (0 : ℝ) 1)) ≤ ENNReal.ofReal B * (α R) ^ 2 := by
  apply finite_oneArm_energy_of_canonical_matching
    (P.speedup (1 / (2 * k.rate z)) (by positivity)) z hz
    (matching_normalization k z hpos)
    (fun e => mul_nonneg (by positivity) (unorderedPairRate_nonneg k e))
    F hmono hex v hv α hcanonical

theorem exists_normalized_matching
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    (k : RateKernel) (P : PoissonGraphicalRealization μ k.unorderedPairRate) :
    ∃ z : Site, ∃ hpos : 0 < k.rate z, z ≠ (0, 0) ∧
      (∀ x, (1 / (2 * k.rate z)) *
        k.unorderedPairRate s(x, PeriodicMatching.partner z x) = 1 / 2) ∧
      ∀ ω, (P.speedup (1 / (2 * k.rate z)) (by positivity)).trajectories ω =
        rescaleTime (1 / (2 * k.rate z)) (P.trajectories ω) := by
  obtain ⟨z, hz, hpos⟩ := k.exists_positive_displacement
  exact ⟨z, hpos, hz, matching_normalization k z hpos, P.speedup_trajectories _ _⟩

theorem almostSureConjecturedDimension_speedup_iff
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (a : ℝ) (ha : 0 < a) :
    AlmostSureConjecturedDimension μ (P.speedup a ha).trajectories ↔
      AlmostSureConjecturedDimension μ P.trajectories := by
  constructor
  · intro H
    apply H.mono
    intro ω hω
    rw [P.speedup_trajectories] at hω
    have H' := hω.rescaleTime (inv_pos.mpr ha)
    have heq : rescaleTime a⁻¹ (rescaleTime a (P.trajectories ω)) = P.trajectories ω := by
      funext t
      unfold rescaleTime
      rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rwa [heq] at H'
  · exact P.almostSureConjecturedDimension_speedup a ha

#print axioms finite_energy_of_canonical_matching
#print axioms exists_normalized_matching
#print axioms almostSureConjecturedDimension_speedup_iff

end ExceptionalTimes.FiniteMatchingNormalization
