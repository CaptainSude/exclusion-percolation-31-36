import ExceptionalTimes.BlockExpansion
import ExceptionalTimes.DimerLaw
import ExceptionalTimes.SignedResponse

/-! Exact two-time dimer expansions and centered quadratic remainders.
These finite laws are the ones used in the independent-block expansion.
Their identification with the graphical clock process is separate. -/

namespace ExceptionalTimes.DimerExpansion

open DimerLaw CenteredBlocks BlockExpansion
open scoped BigOperators Classical

abbrev History := Color × Color

noncomputable def base (h : History) : ℝ := twoTimeWeight 0 h.1 h.2
noncomputable def canonicalInsertion (h : History) : ℝ :=
  twoTimeWeight 1 h.1 h.2 - base h
noncomputable def canonicalLaw (t : ℝ) (h : History) : ℝ :=
  twoTimeWeight (refreshProbability t) h.1 h.2

noncomputable def siteBase (a b : Bool) : ℝ := if a = b then 1 / 2 else 0
noncomputable def siteInsertion (a b : Bool) : ℝ := 1 / 4 - siteBase a b
noncomputable def refreshInsertion (h : History) : ℝ :=
  (siteInsertion (h.1 0) (h.2 0) * siteBase (h.1 1) (h.2 1) +
    siteBase (h.1 0) (h.2 0) * siteInsertion (h.1 1) (h.2 1)) / 2
noncomputable def doubleInsertion (h : History) : ℝ :=
  siteInsertion (h.1 0) (h.2 0) * siteInsertion (h.1 1) (h.2 1)
noncomputable def refreshLaw (t : ℝ) (h : History) : ℝ :=
  (siteBase (h.1 0) (h.2 0) + refreshProbability (t / 2) * siteInsertion (h.1 0) (h.2 0)) *
    (siteBase (h.1 1) (h.2 1) + refreshProbability (t / 2) * siteInsertion (h.1 1) (h.2 1))

theorem base_eq_site_product (h : History) :
    base h = siteBase (h.1 0) (h.2 0) * siteBase (h.1 1) (h.2 1) := by
  obtain ⟨ω, η⟩ := h
  obtain ⟨a, b, rfl⟩ := color_cases ω
  obtain ⟨c, d, rfl⟩ := color_cases η
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [base, twoTimeWeight, siteBase, pair, pair_eq_pair]

theorem canonicalLaw_expansion (t : ℝ) (h : History) :
    canonicalLaw t h = base h + refreshProbability t * canonicalInsertion h := by
  unfold canonicalLaw canonicalInsertion base twoTimeWeight
  ring

theorem refreshLaw_expansion (t : ℝ) (h : History) :
    refreshLaw t h = base h + 2 * refreshProbability (t / 2) * refreshInsertion h +
      (refreshProbability (t / 2)) ^ 2 * doubleInsertion h := by
  rw [base_eq_site_product]
  unfold refreshLaw refreshInsertion doubleInsertion
  ring

theorem canonicalInsertion_centered : ∑ h, canonicalInsertion h = 0 := by
  simp only [canonicalInsertion, base, Finset.sum_sub_distrib, Fintype.sum_prod_type,
    twoTimeWeight_total, sub_self]

theorem refreshInsertion_centered : ∑ h, refreshInsertion h = 0 := by
  simp only [Fintype.sum_prod_type, sum_color]
  norm_num [refreshInsertion, siteInsertion, siteBase, pair]

theorem doubleInsertion_centered : ∑ h, doubleInsertion h = 0 := by
  simp only [Fintype.sum_prod_type, sum_color]
  norm_num [doubleInsertion, siteInsertion, siteBase, pair]

theorem canonicalInsertion_variation : variation canonicalInsertion = 1 / 2 := by
  simp only [variation, Fintype.sum_prod_type, sum_color]
  norm_num [canonicalInsertion, base, twoTimeWeight_formula,
    blackCount, pair, pair_eq_pair, Fin.sum_univ_succ]

theorem refreshInsertion_variation : variation refreshInsertion = 1 := by
  simp only [variation, Fintype.sum_prod_type, sum_color]
  norm_num [refreshInsertion, siteInsertion, siteBase, pair]

theorem doubleInsertion_variation : variation doubleInsertion = 1 := by
  simp only [variation, Fintype.sum_prod_type, sum_color]
  norm_num [doubleInsertion, siteInsertion, siteBase, pair]

theorem canonicalInsertion_response (f : DimerBinaryResponse.Table)
    (test : Bool × Bool → ℝ) :
    (∑ h : History, canonicalInsertion h *
      test (f.eval (h.1 0) (h.1 1), f.eval (h.2 0) (h.2 1))) =
        SignedResponse.pairResponse f DimerBinaryResponse.canonical test := by
  simp only [Fintype.sum_prod_type, sum_color]
  norm_num [canonicalInsertion, base, twoTimeWeight_formula, blackCount, pair,
    pair_eq_pair, Fin.sum_univ_succ, SignedResponse.pairResponse,
    DimerBinaryResponse.canonical]
  ring

theorem refreshInsertion_response (f : DimerBinaryResponse.Table)
    (test : Bool × Bool → ℝ) :
    (∑ h : History, refreshInsertion h *
      test (f.eval (h.1 0) (h.1 1), f.eval (h.2 0) (h.2 1))) =
        SignedResponse.pairResponse f DimerBinaryResponse.refresh test := by
  simp only [Fintype.sum_prod_type, sum_color]
  norm_num [refreshInsertion, siteInsertion, siteBase, pair,
    SignedResponse.pairResponse, DimerBinaryResponse.refresh]
  ring

/-- The very same insertion used in the exact canonical semigroup expansion
has the universal signed bit response used in the sewing argument. -/
theorem canonicalInsertion_pushforward (f : DimerBinaryResponse.Table)
    (hf : DimerBinaryResponse.Increasing f) (test : Bool × Bool → ℝ) :
    (∑ h : History, canonicalInsertion h *
      test (f.eval (h.1 0) (h.1 1), f.eval (h.2 0) (h.2 1))) =
        SignedResponse.canonicalAmplitude f * SignedResponse.bitResponse test := by
  rw [canonicalInsertion_response, SignedResponse.canonical_response f hf]

theorem refreshInsertion_pushforward (f : DimerBinaryResponse.Table)
    (hf : DimerBinaryResponse.Increasing f) (test : Bool × Bool → ℝ) :
    (∑ h : History, refreshInsertion h *
      test (f.eval (h.1 0) (h.1 1), f.eval (h.2 0) (h.2 1))) =
        SignedResponse.refreshAmplitude f * SignedResponse.bitResponse test := by
  rw [refreshInsertion_response, SignedResponse.refresh_response f hf]

noncomputable def canonicalRemainder (t : ℝ) (h : History) : ℝ :=
  (refreshProbability t - t) * canonicalInsertion h
noncomputable def refreshRemainder (t : ℝ) (h : History) : ℝ :=
  (2 * refreshProbability (t / 2) - t) * refreshInsertion h +
    (refreshProbability (t / 2)) ^ 2 * doubleInsertion h

theorem canonicalLaw_linear_remainder (t : ℝ) (h : History) :
    canonicalLaw t h = base h + t * canonicalInsertion h + canonicalRemainder t h := by
  rw [canonicalLaw_expansion]
  unfold canonicalRemainder
  ring

theorem refreshLaw_linear_remainder (t : ℝ) (h : History) :
    refreshLaw t h = base h + t * refreshInsertion h + refreshRemainder t h := by
  rw [refreshLaw_expansion]
  unfold refreshRemainder
  ring

theorem canonicalRemainder_centered (t : ℝ) : ∑ h, canonicalRemainder t h = 0 := by
  simp only [canonicalRemainder, ← Finset.mul_sum, canonicalInsertion_centered, mul_zero]

theorem refreshRemainder_centered (t : ℝ) : ∑ h, refreshRemainder t h = 0 := by
  simp only [refreshRemainder, Finset.sum_add_distrib, ← Finset.mul_sum,
    refreshInsertion_centered, doubleInsertion_centered, mul_zero, add_zero]

theorem canonicalRemainder_variation {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    variation (canonicalRemainder t) ≤ t ^ 2 / 2 := by
  have h := canonical_remainder_variation canonicalInsertion ht ht1
  change variation (fun h => ((1 - Real.exp (-t)) - t) * canonicalInsertion h) ≤ _
  simpa only [canonicalInsertion_variation, div_eq_mul_inv, one_mul] using h

theorem refreshProbability_le_time (t : ℝ) :
    refreshProbability t ≤ t := by
  have h := Real.add_one_le_exp (-t)
  unfold refreshProbability
  linarith

theorem refreshRemainder_variation {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    variation (refreshRemainder t) ≤ 3 * t ^ 2 / 4 := by
  have ht2 : 0 ≤ t / 2 := by linarith
  have ht21 : t / 2 ≤ 1 := by linarith
  have hr := refresh_time_remainder ht2 ht21
  have hq0 := refreshProbability_nonneg ht2
  have hq := refreshProbability_le_time (t / 2)
  have hfirst : |2 * refreshProbability (t / 2) - t| ≤ t ^ 2 / 2 := by
    calc
      _ = 2 * |refreshProbability (t / 2) - t / 2| := by
        rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul]
        congr 1
        ring
      _ ≤ 2 * (t / 2) ^ 2 := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = _ := by ring
  have hsecond : (refreshProbability (t / 2)) ^ 2 ≤ t ^ 2 / 4 := by nlinarith
  unfold refreshRemainder
  apply (variation_add _ _).trans
  rw [variation_smul, variation_smul, refreshInsertion_variation,
    doubleInsertion_variation, mul_one, mul_one,
    abs_of_nonneg (sq_nonneg (refreshProbability (t / 2)))]
  linarith

end ExceptionalTimes.DimerExpansion

#print axioms ExceptionalTimes.DimerExpansion.canonicalLaw_linear_remainder
#print axioms ExceptionalTimes.DimerExpansion.refreshLaw_linear_remainder
#print axioms ExceptionalTimes.DimerExpansion.refreshRemainder_variation
#print axioms ExceptionalTimes.DimerExpansion.canonicalInsertion_pushforward
#print axioms ExceptionalTimes.DimerExpansion.refreshInsertion_pushforward
