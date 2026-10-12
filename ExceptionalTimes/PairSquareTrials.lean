import ExceptionalTimes.PairSquareSewing
import ExceptionalTimes.DimerExpansion

/-!
Literal dimer weights agree with the concrete pair-history response, and
the finite many-trial averaging argument uses probabilities of the
actual source E. No pair/square replacement error is an input.
-/

open scoped BigOperators Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance DimerBinaryResponse

/-- Exact identification with the insertion used in the actual finite
canonical semigroup expansion, for every exterior history test. -/
theorem canonical_weight_eq_raw (background : TwoTimeConfiguration)
    (x z : Site) (F : TwoTimeConfiguration → ℝ) :
    (∑ h : DimerExpansion.History, DimerExpansion.canonicalInsertion h *
      F (pairHistory background x z (h.1 0, h.1 1) (h.2 0, h.2 1))) =
      rawPairResponse DimerBinaryResponse.canonical background x z F := by
  simp only [Fintype.sum_prod_type, DimerLaw.sum_color]
  norm_num [DimerExpansion.canonicalInsertion, DimerExpansion.base,
    DimerLaw.twoTimeWeight_formula, DimerLaw.blackCount, DimerLaw.pair,
    DimerLaw.pair_eq_pair, Fin.sum_univ_succ, rawPairResponse,
    DimerBinaryResponse.canonical]
  ring

theorem refresh_weight_eq_raw (background : TwoTimeConfiguration)
    (x z : Site) (F : TwoTimeConfiguration → ℝ) :
    (∑ h : DimerExpansion.History, DimerExpansion.refreshInsertion h *
      F (pairHistory background x z (h.1 0, h.1 1) (h.2 0, h.2 1))) =
      rawPairResponse DimerBinaryResponse.refresh background x z F := by
  simp only [Fintype.sum_prod_type, DimerLaw.sum_color]
  norm_num [DimerExpansion.refreshInsertion, DimerExpansion.siteInsertion,
    DimerExpansion.siteBase, DimerLaw.pair, rawPairResponse,
    DimerBinaryResponse.refresh]
  ring

section TrialAveraging

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

def AllFailed (U : I → Ω → Prop) (ω : Ω) : Prop := ∀ i, ¬ U i ω

def UniqueSuccess (U : I → Ω → Prop) (j : I) (ω : Ω) : Prop :=
  U j ω ∧ ∀ i, i ≠ j → ¬ U i ω

omit [Fintype Ω] in
theorem unique_success_indicator_sum (E : Ω → Prop) (U : I → Ω → Prop) (ω : Ω) :
    (∑ j, indicator (E ω ∧ UniqueSuccess U j ω)) ≤ indicator (E ω) := by
  classical
  by_cases h : ∃ j, E ω ∧ UniqueSuccess U j ω
  · obtain ⟨j, hj⟩ := h
    have hz : ∀ i, i ≠ j → indicator (E ω ∧ UniqueSuccess U i ω) = 0 := by
      intro i hij
      have hn : ¬ (E ω ∧ UniqueSuccess U i ω) := by
        intro hi
        exact hj.2.2 i hij hi.2.1
      simp [indicator, hn]
    rw [Finset.sum_eq_single j]
    · simp [indicator, hj.1, hj.2]
    · intro i _ hij
      exact hz i hij
    · simp
  · have hz : ∀ j, indicator (E ω ∧ UniqueSuccess U j ω) = 0 := by
      intro j
      have hn : ¬ (E ω ∧ UniqueSuccess U j ω) := fun hj => h ⟨j,hj⟩
      simp [indicator, hn]
    simp only [hz, Finset.sum_const_zero]
    exact indicator_nonneg _

theorem unique_success_probability_sum (μ : FiniteLaw Ω)
    (E : Ω → Prop) (U : I → Ω → Prop) :
    (∑ j, probability μ (fun ω => E ω ∧ UniqueSuccess U j ω)) ≤ probability μ E := by
  have h := μ.expect_mono (unique_success_indicator_sum E U)
  simp only [FiniteLaw.expect, Finset.mul_sum] at h
  simp only [probability, FiniteLaw.expect]
  rw [Finset.sum_comm]
  exact h

/-- The finite form of the source's many-trial argument. The inputs are
exactly one-trial comparisons and disqualifications; independence of
trials conditional on E is not assumed. -/
theorem many_trial_average (μ : FiniteLaw Ω) (E : Ω → Prop)
    (U : I → Ω → Prop) (bad : I → Ω → Prop) (C : ℝ) (hC : 0 ≤ C)
    (oneTrial : ∀ j,
      probability μ (fun ω => E ω ∧ AllFailed U ω ∧ ¬ bad j ω) ≤
        C * probability μ (fun ω => E ω ∧ UniqueSuccess U j ω)) :
    (Fintype.card I : ℝ) * probability μ (fun ω => E ω ∧ AllFailed U ω) ≤
      C * probability μ E + ∑ j, probability μ (fun ω => E ω ∧ bad j ω) := by
  have hsplit (j : I) :
      probability μ (fun ω => E ω ∧ AllFailed U ω) ≤
      probability μ (fun ω => E ω ∧ AllFailed U ω ∧ ¬ bad j ω) +
      probability μ (fun ω => E ω ∧ bad j ω) := by
    simp only [probability]
    rw [← FiniteLaw.expect_add]
    apply μ.expect_mono
    intro ω
    classical
    by_cases he : E ω <;> by_cases hn : AllFailed U ω <;> by_cases hb : bad j ω <;>
      simp [indicator, he, hn, hb]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    (hsplit j).trans (add_le_add (oneTrial j) le_rfl))
  have hdisjoint := unique_success_probability_sum μ E U
  have hmul := mul_le_mul_of_nonneg_left hdisjoint hC
  calc
    _ ≤ ∑ j, (C * probability μ (fun ω => E ω ∧ UniqueSuccess U j ω) +
        probability μ (fun ω => E ω ∧ bad j ω)) := by simpa using hsum
    _ = C * (∑ j, probability μ (fun ω => E ω ∧ UniqueSuccess U j ω)) +
        ∑ j, probability μ (fun ω => E ω ∧ bad j ω) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add hmul le_rfl

/-- Each disqualification costs rho times the same arm normalization.
Averaging leaves rho, not number-of-trials times rho. -/
theorem many_trial_relative_bound (μ : FiniteLaw Ω) (E : Ω → Prop)
    (U : I → Ω → Prop) (bad : I → Ω → Prop)
    (C C₀ ρ a : ℝ) (hC : 0 ≤ C) (hcount : 0 < Fintype.card I)
    (oneTrial : ∀ j,
      probability μ (fun ω => E ω ∧ AllFailed U ω ∧ ¬ bad j ω) ≤
        C * probability μ (fun ω => E ω ∧ UniqueSuccess U j ω))
    (necessary : probability μ E ≤ C₀ * a)
    (disqualification : ∀ j, probability μ (fun ω => E ω ∧ bad j ω) ≤ ρ * a) :
    probability μ (fun ω => E ω ∧ AllFailed U ω) ≤
      (ρ + C * C₀ / (Fintype.card I : ℝ)) * a := by
  have h := many_trial_average μ E U bad C hC oneTrial
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun j _ => disqualification j)
  have hc := mul_le_mul_of_nonneg_left necessary hC
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast hcount
  have hsum : (∑ j, probability μ (fun ω => E ω ∧ bad j ω)) ≤
      (Fintype.card I : ℝ) * (ρ * a) := by simpa using hd
  apply (mul_le_mul_iff_right₀ hn).mp
  have heq : ((ρ + C * C₀ / (Fintype.card I : ℝ)) * a) *
      (Fintype.card I : ℝ) =
      C * (C₀ * a) + (Fintype.card I : ℝ) * (ρ * a) := by
    field_simp [ne_of_gt hn]
    ring
  rw [mul_comm (Fintype.card I : ℝ) ((ρ + C * C₀ / (Fintype.card I : ℝ)) * a), heq]
  nlinarith

end TrialAveraging

/-- The published one-trial criterion is instantiated on the actual E,
the actual two independent finite fair site fields, and the complete
list of trial success tests. -/
theorem source_many_trial_bound {Λ : Finset Site} {n : ℕ}
    (mic sq : Probe) (success : Fin n → Sources Λ → Bool)
    (bad : Fin n → Sources Λ → Prop) (C C₀ ρ a : ℝ)
    (hC : 0 ≤ C) (hn : 0 < n)
    (oneTrial : ∀ j,
      probability (sourceLaw Λ) (fun ω =>
        SourceE mic sq (complete ω.1) (complete ω.2) ∧
        (∀ i, success i ω = false) ∧ ¬ bad j ω) ≤
      C * probability (sourceLaw Λ) (fun ω =>
        SourceE mic sq (complete ω.1) (complete ω.2) ∧
        success j ω = true ∧ ∀ i, i ≠ j → success i ω = false))
    (necessary : probability (sourceLaw Λ)
      (fun ω => SourceE mic sq (complete ω.1) (complete ω.2)) ≤ C₀ * a)
    (disqualification : ∀ j, probability (sourceLaw Λ) (fun ω =>
      SourceE mic sq (complete ω.1) (complete ω.2) ∧ bad j ω) ≤ ρ * a) :
    probability (sourceLaw Λ) (fun ω =>
      SourceE mic sq (complete ω.1) (complete ω.2) ∧
        AdaptiveExchange.select success (List.finRange n) ω = none) ≤
      (ρ + C * C₀ / (n : ℝ)) * a := by
  have h := many_trial_relative_bound (sourceLaw Λ)
    (fun ω => SourceE mic sq (complete ω.1) (complete ω.2))
    (fun i ω => success i ω = true) bad C C₀ ρ a hC
    (by simpa using hn) (by simpa [AllFailed, UniqueSuccess] using oneTrial)
    necessary disqualification
  simpa [AllFailed, AdaptiveExchange.select, List.find?_eq_none] using h


/-- Monotonicity is proved for the actual graph path crossing. -/
theorem GraphQuad.crossing_mono (Q : GraphQuad) {ω η : Configuration}
    (h : ∀ v, ω v = true → η v = true) (hc : Q.Crossing ω) : Q.Crossing η := by
  obtain ⟨u,hu,v,hv,p,hp⟩ := hc
  exact ⟨u,hu,v,hv,p,fun z hz => ⟨(hp z hz).1, h z (hp z hz).2⟩⟩

theorem square_crossing_mono (Q : GraphQuad) (D : Finset Site) (ω : Configuration) :
    Q.test (force D ω false) = true → Q.test (force D ω true) = true := by
  simp only [GraphQuad.test, decide_eq_true_eq]
  apply Q.crossing_mono
  intro v hv
  by_cases hD : v ∈ D
  · simp [force, hD]
  · simpa [force, hD] using hv

noncomputable def boolValue (b : Bool) : ℝ := if b then 1 else 0

noncomputable def GraphQuad.jump (Q : GraphQuad) (η : TwoTimeConfiguration) : ℝ :=
  if Q.test (η false) ≠ Q.test (η true) then 1 else 0

/-- Exact factor two between the imposed W-square jump amplitude and
the source's one-time Delta-square pivotal amplitude, for each exterior.
There is no random monochromatic-square event in this identity. -/
theorem square_jump_half_pivotal (Q : GraphQuad) (D : Finset Site) (ω : Configuration) :
    rawSquareResponse D (fun _ => ω) Q.jump =
      (boolValue (Q.test (force D ω true)) -
        boolValue (Q.test (force D ω false))) / 2 := by
  have hm := square_crossing_mono Q D ω
  cases h0 : Q.test (force D ω false) <;>
    cases h1 : Q.test (force D ω true) <;>
    simp_all [rawSquareResponse, SignedResponse.bitResponse, GraphQuad.jump,
      squareHistory, boolValue]; norm_num

#print axioms square_jump_half_pivotal

end ExceptionalTimes.PairSquareSewing

#print axioms ExceptionalTimes.PairSquareSewing.canonical_weight_eq_raw
#print axioms ExceptionalTimes.PairSquareSewing.refresh_weight_eq_raw
#print axioms ExceptionalTimes.PairSquareSewing.many_trial_relative_bound
#print axioms ExceptionalTimes.PairSquareSewing.source_many_trial_bound






