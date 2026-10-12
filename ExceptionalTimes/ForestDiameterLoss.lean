import ExceptionalTimes.ForestLifeCount
import ExceptionalTimes.ForestProbes

/-! Literal logarithmic diameter losses of the constructed probes are bounded
by the already proved numerical charges. -/

open scoped BigOperators Classical
open MeasureTheory Set

namespace ExceptionalTimes.ForestDiameterLoss

open KruskalLives ForestLifeGeometry ForestGeometry ForestCharge ForestLifeCount ForestProbes

noncomputable def logarithmicLoss (u v size : ℝ) : ℝ :=
  ∫ t in u..v, if t < size then 1/t else 0

theorem logarithmicLoss_le {u v size : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : 0 ≤ size) :
    logarithmicLoss u v size ≤ ∫ t in u..v, size/t^2 := by
  have hinv : IntervalIntegrable (fun t : ℝ => 1/t) volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (hu.trans_le ht.1))
  have hleft : IntervalIntegrable (fun t : ℝ => if t < size then 1/t else 0) volume u v := by
    rw [intervalIntegrable_iff] at hinv ⊢
    exact hinv.indicator measurableSet_Iio
  have hright : IntervalIntegrable (fun t : ℝ => size/t^2) volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (hu.trans_le ht.1)))
  apply intervalIntegral.integral_mono_on huv hleft hright
  intro t ht
  have ht0 := hu.trans_le ht.1
  by_cases hts : t < size
  · rw [ite_eq_left hts]
    apply (div_le_div_iff₀ ht0 (sq_pos_of_pos ht0)).mpr
    nlinarith
  · rw [ite_eq_right hts]
    exact div_nonneg hs (sq_nonneg t)

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

theorem life_logarithmicLoss_le (fixed : V → Prop) (position : V → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin) {S : Set V}
    (htimes : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    logarithmicLoss (birth fixed position cutoff stop S) (death fixed position cutoff stop S)
      (span fixed position cutoff S + margin) ≤
    (∑ e ∈ internalEdges (recorded fixed position cutoff) S,
      ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
        clippedEdgeLength position cutoff e / t^2) +
    (∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S, margin/t^2) := by
  have hu := hb.trans_le (cutoff_le_birth htimes)
  have hv := hu.trans hlife
  apply (logarithmicLoss_le hu hlife.le (add_nonneg (span_nonneg _ _ _ _) hm)).trans_eq
  rw [integral_edge_charge hu hv]
  simp only [integral_edge_charge hu hv, span, add_div, Finset.sum_div, Finset.sum_sub_distrib]
  ring

/-- The total literal logarithmic loss of the actual annuli is linear in k.
This includes empty probes caused by their diameter enlargement. -/
theorem total_logarithmicLoss_le (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin)
    (lives : Finset (Set (Fin (k+J))))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, logarithmicLoss (birth fixed position cutoff stop S) (death fixed position cutoff stop S)
      (span fixed position cutoff S + margin)) ≤ (k : ℝ) + (2*k : ℝ)*margin/cutoff := by
  apply (Finset.sum_le_sum (fun S hS => life_logarithmicLoss_le fixed position hb hm
    (htimes S hS) (hlife S hS))).trans
  rw [Finset.sum_add_distrib]
  exact total_charge_le k J fixed hroots position hb hm lives htimes hrootless hlife

theorem exponential_loss_le (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop margin g : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin) (hg : 0 ≤ g)
    (lives : Finset (Set (Fin (k+J))))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    Real.exp (g * ∑ S ∈ lives,
      logarithmicLoss (birth fixed position cutoff stop S) (death fixed position cutoff stop S)
        (span fixed position cutoff S + margin)) ≤
      Real.exp (g * (1 + 2*margin/cutoff)) ^ k := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (total_logarithmicLoss_le k J fixed hroots position hb hm lives htimes hrootless hlife) hg
  convert h using 1
  ring

#print axioms total_logarithmicLoss_le
#print axioms exponential_loss_le

end ExceptionalTimes.ForestDiameterLoss
