import ExceptionalTimes.PeriodicMatching
import ExceptionalTimes.RateKernel

/-!
Connect the explicit periodic matching to a general translation-invariant
exchange kernel. Canonical rate-one pair refresh has swap rate one-half;
the deterministic comparison factor is therefore exactly twice k(z).
This file proves the rate comparison, not the unbounded-operator theorem.
-/

namespace ExceptionalTimes

open PeriodicMatching

theorem partner_exchange_rate (k : RateKernel) (z x : ℤ × ℤ) :
    k.pairRate x (partner z x) = k.rate z := by
  rcases partner_displacement z x with h | h
  · rw [h, RateKernel.pairRate]
    have heq : PeriodicMatching.add x z - x = z := by
      apply Prod.ext <;> simp [PeriodicMatching.add]
    rw [heq]
  · rw [h, RateKernel.pairRate]
    have heq : PeriodicMatching.sub x z - x = -z := by
      apply Prod.ext <;> simp [PeriodicMatching.sub]
    rw [heq, k.symmetric]

/-- Swap rates associated with canonical rate-one refresh on a matching. -/
noncomputable def canonicalMatchingRate (z x y : ℤ × ℤ) : ℝ :=
  if partner z x = y then 1 / 2 else 0

theorem canonicalMatchingRate_symmetric (z : ℤ × ℤ) (hz : z ≠ 0)
    (x y : ℤ × ℤ) : canonicalMatchingRate z x y = canonicalMatchingRate z y x := by
  have heq : partner z x = y ↔ partner z y = x := by
    constructor
    · intro h
      rw [← h, partner_involutive z hz]
    · intro h
      rw [← h, partner_involutive z hz]
  simp only [canonicalMatchingRate, heq]

theorem canonicalMatchingRate_diagonal (z : ℤ × ℤ) (hz : z ≠ 0)
    (x : ℤ × ℤ) : canonicalMatchingRate z x x = 0 := by
  simp only [canonicalMatchingRate, ite_eq_right (partner_ne_self z hz x)]

theorem matching_rate_domination (k : RateKernel) (z x y : ℤ × ℤ) :
    (2 * k.rate z) * canonicalMatchingRate z x y ≤ k.pairRate x y := by
  by_cases h : partner z x = y
  · rw [canonicalMatchingRate, ite_eq_left h, ← h, partner_exchange_rate]
    have heq : (2 * k.rate z) * (1 / 2 : ℝ) = k.rate z := by ring
    exact heq.le
  · rw [canonicalMatchingRate, ite_eq_right h, mul_zero]
    exact k.pairRate_nonneg x y

/-- A genuinely allowed displacement supports a positive comparison with a
fixed-point-free periodic matching. The existence of the matching is proved
by the integer construction rather than postulated in the kernel interface. -/
theorem exists_dominated_matching (k : RateKernel) :
    ∃ z : ℤ × ℤ, z ≠ 0 ∧ 0 < k.rate z ∧
      (∀ x, partner z (partner z x) = x) ∧
      (∀ x, partner z x ≠ x) ∧
      (∀ x y, (2 * k.rate z) * canonicalMatchingRate z x y ≤ k.pairRate x y) := by
  obtain ⟨z, hz, hrate⟩ := k.exists_positive_displacement
  exact ⟨z, hz, hrate, partner_involutive z hz, partner_ne_self z hz,
    matching_rate_domination k z⟩

end ExceptionalTimes

#print axioms ExceptionalTimes.partner_exchange_rate
#print axioms ExceptionalTimes.canonicalMatchingRate_symmetric
#print axioms ExceptionalTimes.matching_rate_domination
#print axioms ExceptionalTimes.exists_dominated_matching
