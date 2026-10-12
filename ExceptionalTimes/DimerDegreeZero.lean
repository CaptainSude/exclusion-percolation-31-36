import ExceptionalTimes.EffectiveDimerInsertion

/-! At degree zero every expansion is the same static fair-field integral. -/
open scoped Classical BigOperators
namespace ExceptionalTimes.DimerDegreeZero
open PairSquareSewing EffectiveDimerInsertion ExpansionLimit BlockExpansion

variable {B : Type*} [Fintype B]

theorem scaledCoefficient_independent (r₁ r₂ : Rule) (f : (B→DimerExpansion.History)→ℝ)
    (a b : ℝ) : scaledCoefficient r₁ f a 0=scaledCoefficient r₂ f b 0 := by
  simp [scaledCoefficient,coefficient,Finset.card_eq_zero,Finset.sum_filter,selectedKernel]

theorem difference_eq_zero (f : (B→DimerExpansion.History)→ℝ) (a b : ℝ) :
    scaledCoefficient .canonical f a 0-scaledCoefficient .refresh f b 0=0 := by
  rw [scaledCoefficient_independent .canonical .refresh f a b,sub_self]

#print axioms difference_eq_zero
end ExceptionalTimes.DimerDegreeZero
