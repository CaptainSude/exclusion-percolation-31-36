import ExceptionalTimes.CanonicalRadialLaw

/-! Finite-observation approximation preserves two-time probabilities.
No approximation theorem or dynamical crossing transfer is assumed to
have been proved here. Their separate quantitative errors are retained. -/

namespace ExceptionalTimes.PairedEventTransfer

open EnvironmentVariance
open scoped Classical

theorem pair_indicator_error (E₀ E₁ F₀ F₁ : Prop) :
    |indicator (E₀ ∧ E₁)-indicator (F₀ ∧ F₁)| ≤
      indicator (¬(E₀ ↔ F₀)) + indicator (¬(E₁ ↔ F₁)) := by
  by_cases hE₀ : E₀ <;> by_cases hE₁ : E₁ <;>
    by_cases hF₀ : F₀ <;> by_cases hF₁ : F₁ <;>
    simp [indicator,hE₀,hE₁,hF₀,hF₁]

/-- Each replica pays only its one-time approximation error. No
independence of the two replicas is needed. -/
theorem paired_probability_error {S : Type*} [Fintype S]
    (ν : FiniteLaw S) (E₀ E₁ F₀ F₁ : S → Prop) :
    |probability ν (fun x => E₀ x ∧ E₁ x) -
      probability ν (fun x => F₀ x ∧ F₁ x)| ≤
      probability ν (fun x => ¬(E₀ x ↔ F₀ x)) +
      probability ν (fun x => ¬(E₁ x ↔ F₁ x)) := by
  unfold probability
  rw [← ν.expect_sub,← ν.expect_add]
  exact (ν.abs_expect_le _).trans (ν.expect_mono
    (fun x => pair_indicator_error (E₀ x) (E₁ x) (F₀ x) (F₁ x)))

/-- Once a crossing-vector approximation is supplied for each marginal,
the two-law paired-event error is bounded by four marginal errors and
the actual finite-observation comparison error. -/
theorem paired_event_transfer {S T : Type*} [Fintype S] [Fintype T]
    (ν : FiniteLaw S) (μ : FiniteLaw T)
    (E₀ E₁ F₀ F₁ : S → Prop) (G₀ G₁ H₀ H₁ : T → Prop)
    {ε δ : ℝ}
    (hν₀ : probability ν (fun x => ¬(E₀ x ↔ F₀ x)) ≤ ε)
    (hν₁ : probability ν (fun x => ¬(E₁ x ↔ F₁ x)) ≤ ε)
    (hμ₀ : probability μ (fun x => ¬(G₀ x ↔ H₀ x)) ≤ ε)
    (hμ₁ : probability μ (fun x => ¬(G₁ x ↔ H₁ x)) ≤ ε)
    (hfinite : |probability ν (fun x => F₀ x ∧ F₁ x) -
      probability μ (fun x => H₀ x ∧ H₁ x)| ≤ δ) :
    |probability ν (fun x => E₀ x ∧ E₁ x) -
      probability μ (fun x => G₀ x ∧ G₁ x)| ≤ 4*ε+δ := by
  have hν := paired_probability_error ν E₀ E₁ F₀ F₁
  have hμ := paired_probability_error μ G₀ G₁ H₀ H₁
  have ht₁ := abs_sub_le
    (probability ν (fun x => E₀ x ∧ E₁ x))
    (probability ν (fun x => F₀ x ∧ F₁ x))
    (probability μ (fun x => G₀ x ∧ G₁ x))
  have ht₂ := abs_sub_le
    (probability ν (fun x => F₀ x ∧ F₁ x))
    (probability μ (fun x => H₀ x ∧ H₁ x))
    (probability μ (fun x => G₀ x ∧ G₁ x))
  rw [abs_sub_comm (probability μ (fun x => H₀ x ∧ H₁ x))] at ht₂
  linarith

#print axioms paired_probability_error
#print axioms paired_event_transfer

end ExceptionalTimes.PairedEventTransfer
