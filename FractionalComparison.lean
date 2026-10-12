import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Bounded fractional inverse comparison

This pilot uses the existing C-star-algebra functional calculus. It proves
an order statement for bounded, strictly positive elements; it does not
construct unbounded Markov generators, identify their closed quadratic
forms, or establish the time-energy/resolvent representation.

The positive-power and inverse-order inputs below are theorems already
proved in mathlib. No external mathematical results are assumed here.
-/

namespace ExceptionalTimesPilot

/-- Inverse powers of exponent at most one reverse the order of strictly
positive bounded operators. No commutation hypothesis is used. -/
theorem fractional_inverse_order
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (hab : a ≤ b) (ha : IsStrictlyPositive a) :
    CFC.rpow (Ring.inverse b) s ≤ CFC.rpow (Ring.inverse a) s :=
  (CFC.monotone_rpow hs) (CStarAlgebra.ringInverse_le_ringInverse hab ha)

/-- Adding a common strictly positive baseline to nonnegative bounded
generators allows the same comparison. Choosing the baseline to be the
identity gives the bounded resolvents relevant to the manuscript. -/
theorem shifted_fractional_inverse_order
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {r a b : A} {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (hr : IsStrictlyPositive r) (ha : 0 ≤ a) (hab : a ≤ b) :
    CFC.rpow (Ring.inverse (r + b)) s ≤
      CFC.rpow (Ring.inverse (r + a)) s :=
  fractional_inverse_order hs (add_le_add_right hab r) (hr.add_nonneg ha)

end ExceptionalTimesPilot

#print axioms ExceptionalTimesPilot.fractional_inverse_order
#print axioms ExceptionalTimesPilot.shifted_fractional_inverse_order
