import ExceptionalTimes.ForestArmWeights

/-! The forest estimates for arbitrary finite vertex types. All estimates
refer to the same recorded graph; no ordering-dependent reconstruction or
unproved invariance under relabelling is used. -/

open scoped BigOperators Classical
open Set
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.GenericForestArmWeights

open SimpleGraph RootKruskal KruskalComponents KruskalLedger
open ArmEnlargement ForestDiameterLoss ForestProbes ForestTelescope KruskalLives
open ForestLifeGeometry ForestGeometry ForestArmWeights

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

theorem greedy_edge_card (fixed : V → Prop) (es : List (V × V)) :
    (greedy fixed es).edgeFinset.card = acceptedCount fixed es := by
  induction es with
  | nil => simp [greedy, acceptedCount]
  | cons e es ih =>
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · have hG : greedy fixed (e :: es) = greedy fixed es := by simp only [greedy, step, ite_eq_left he]
      rw [edgeFinset_congr _ _ hG]
      simpa only [acceptedCount, ite_eq_left he, Nat.add_zero] using ih
    · have hne : e.1 ≠ e.2 := fun h => he (h ▸ Reachable.rfl)
      have hnmem : s(e.1,e.2) ∉ (greedy fixed es).edgeFinset := fun h =>
        he (((mem_edgeFinset.mp h : (greedy fixed es).Adj e.1 e.2).reachable).mono le_sup_left)
      have hG : greedy fixed (e :: es) = greedy fixed es ⊔ edge e.1 e.2 := by
        simp only [greedy, step, ite_eq_right he]
      rw [edgeFinset_congr _ _ hG]
      simp only [edgeFinset_sup, edgeFinset_single_edge _ _ hne,
        Finset.union_singleton, Finset.card_insert_of_notMem hnmem, ih,
        acceptedCount, ite_eq_right he]

theorem recorded_edge_card_le (fixed : V → Prop) (position : V → X) (cutoff : ℝ) :
    (recorded fixed position cutoff).edgeFinset.card ≤ Fintype.card {v // ¬ fixed v} := by
  have h := ungrounded_greedy_card fixed (SortedKruskal.sortedEdges position cutoff)
  change (greedy fixed (SortedKruskal.sortedEdges position cutoff)).edgeFinset.card ≤ _
  rw [greedy_edge_card]
  omega

theorem lives_card_le_twice (k : ℕ) (fixed : V → Prop)
    (hfree : Fintype.card {v // ¬ fixed v}=k) (position : V → X)
    {cutoff stop : ℝ} (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    lives.card ≤ 2*k := by
  have h := ForestLifeCount.lives_card_le fixed position lives htimes hrootless hlife
  have he := recorded_edge_card_le fixed position cutoff
  rw [hfree] at h he
  omega

theorem total_charge_le (k : ℕ) (fixed : V → Prop)
    (hfree : Fintype.card {v // ¬ fixed v}=k) (position : V → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin)
    (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, ∑ e ∈ internalEdges (recorded fixed position cutoff) S,
      ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
        clippedEdgeLength position cutoff e / t^2) +
    (∑ S ∈ lives, ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
      margin/t^2) ≤ (k : ℝ) + (2*k : ℝ)*margin/cutoff := by
  apply add_le_add
  · apply (ForestCharge.total_recorded_charge_le_card fixed position hb lives htimes hrootless hlife).trans
    have h := recorded_edge_card_le fixed position cutoff
    rw [hfree] at h
    exact_mod_cast h
  · apply (ForestCharge.enlargement_charge_le fixed position hb hm lives htimes hlife).trans
    apply div_le_div_of_nonneg_right _ hb.le
    apply mul_le_mul_of_nonneg_right _ hm
    exact_mod_cast lives_card_le_twice k fixed hfree position lives htimes hrootless hlife

theorem total_logarithmicLoss_le (k : ℕ) (fixed : V → Prop)
    (hfree : Fintype.card {v // ¬ fixed v}=k) (position : V → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin)
    (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, logarithmicLoss (birth fixed position cutoff stop S) (death fixed position cutoff stop S)
      (span fixed position cutoff S + margin)) ≤ (k : ℝ) + (2*k : ℝ)*margin/cutoff := by
  apply (Finset.sum_le_sum (fun S hS => life_logarithmicLoss_le fixed position hb hm
    (htimes S hS) (hlife S hS))).trans
  rw [Finset.sum_add_distrib]
  exact total_charge_le k fixed hfree position hb hm lives htimes hrootless hlife

theorem exponential_loss_le (k : ℕ) (fixed : V → Prop)
    (hfree : Fintype.card {v // ¬ fixed v}=k) (position : V → X)
    {cutoff stop margin g : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin) (hg : 0 ≤ g)
    (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    Real.exp (g * ∑ S ∈ lives,
      logarithmicLoss (birth fixed position cutoff stop S) (death fixed position cutoff stop S)
        (span fixed position cutoff S + margin)) ≤
      Real.exp (g*(1+2*margin/cutoff))^k := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (total_logarithmicLoss_le k fixed hfree position hb hm lives htimes hrootless hlife) hg
  convert h using 1
  ring

theorem positiveLives_card_le (k : ℕ) (fixed : V → Prop)
    (hfree : Fintype.card {v // ¬ fixed v}=k) (position : V → X) (cutoff stop : ℝ) :
    (positiveLives fixed position cutoff stop).card ≤ 2*k := by
  apply lives_card_le_twice k fixed hfree position
  · intro S hS
    exact (positiveLives_spec fixed position cutoff stop hS).1
  · intro S hS
    exact (positiveLives_spec fixed position cutoff stop hS).2.1
  · intro S hS
    exact (positiveLives_spec fixed position cutoff stop hS).2.2

theorem actual_forest_arm_product (k J : ℕ) (hcard : Fintype.card V=k+J) (fixed : V → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : V → X)
    {cutoff stop margin C Q g : ℝ} (hb : 0 < cutoff) (hcut : cutoff ≤ stop)
    (hm : 0 ≤ margin) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hg : 0 ≤ g)
    (α : ℝ → ℝ → ℝ) (hα : ∀ a b, 0 ≤ α a b) (p : ℝ → ℝ)
    (hpnz : ∀ t, p t ≠ 0) (hstop : p stop = 1)
    (hp : ∀ t, 0 < t → t ≤ stop → 0 < p t)
    (hquasi : ∀ a b, 0 < a → a < b → b ≤ stop → α a b ≤ Q * (p a / p b))
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    (∏ S ∈ positiveLives fixed position cutoff stop, lifeCost fixed position cutoff stop margin α S) ≤
      ((Q*C^2*256^g)^2 * Real.exp (g*(1+4*margin/cutoff)))^k *
        (p cutoff^k /
          ∏ e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset,
            p (clippedEdgeLength position cutoff e)) := by
  have hfree : Fintype.card {a // ¬ fixed a} = k := by
    rw [Fintype.card_subtype_compl, hcard, hroots]
    omega
  let L := positiveLives fixed position cutoff stop
  let K := Q*C^2*256^g
  let loss := fun S => logarithmicLoss (birth fixed position cutoff stop S)
    (death fixed position cutoff stop S) (span fixed position cutoff S + 2*margin)
  let ratio := fun S => p (birth fixed position cutoff stop S) / p (death fixed position cutoff stop S)
  have hspec := fun S (hS : S ∈ L) => positiveLives_spec fixed position cutoff stop hS
  have hrpos : ∀ S ∈ L, 0 ≤ ratio S := by
    intro S hS
    have h := hspec S hS
    have hu := hb.trans_le (cutoff_le_birth h.1)
    have hv := hu.trans h.2.2
    exact div_nonneg (hp _ hu (h.2.2.le.trans (death_le_stop h.1))).le
      (hp _ hv (death_le_stop h.1)).le
  have hK : 1 ≤ K := by
    have hpw : (1:ℝ) ≤ 256^g := Real.one_le_rpow (by norm_num) hg
    have hc2 : (1:ℝ) ≤ C^2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hQ hc2) hpw
  have hbound : (∏ S ∈ L, lifeCost fixed position cutoff stop margin α S) ≤
      K^L.card * Real.exp (g * ∑ S ∈ L, loss S) * ∏ S ∈ L, ratio S := by
    calc
      _ ≤ ∏ S ∈ L, K * Real.exp (g*loss S) * ratio S := by
        apply Finset.prod_le_prod₀
        · intro S _hS
          exact separatedArmCost_nonneg α hα _ _
        · intro S hS
          have h := hspec S hS
          exact buffered_armCost_le α p (hb.trans_le (cutoff_le_birth h.1)) h.2.2.le
            (death_le_stop h.1) hC hQ hg hp hquasi hlower
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          ← Real.exp_sum, ← Finset.mul_sum]
  have hcount : K^L.card ≤ K^(2*k) :=
    pow_le_pow_right₀ hK (positiveLives_card_le k fixed hfree position cutoff stop)
  have hcharge : Real.exp (g * ∑ S ∈ L, loss S) ≤
      Real.exp (g*(1+4*margin/cutoff))^k := by
    have h := exponential_loss_le k fixed hfree position (margin := 2*margin) hb
      (mul_nonneg (by norm_num) hm) hg L
      (fun S hS => (hspec S hS).1) (fun S hS => (hspec S hS).2.1)
      (fun S hS => (hspec S hS).2.2)
    simpa only [show (2:ℝ)*(2*margin) = 4*margin by ring] using h
  have hprod : 0 ≤ ∏ S ∈ L, ratio S := Finset.prod_nonneg hrpos
  have htel := actual_forest_telescope fixed position cutoff stop hcut p hpnz hstop
  have hfree : Fintype.card {a // ¬ fixed a} = k := by
    rw [Fintype.card_subtype_compl, hcard, hroots]
    omega
  rw [hfree] at htel
  calc
    _ ≤ K^L.card * Real.exp (g * ∑ S ∈ L, loss S) * ∏ S ∈ L, ratio S := hbound
    _ ≤ K^(2*k) * Real.exp (g*(1+4*margin/cutoff))^k * ∏ S ∈ L, ratio S :=
      mul_le_mul_of_nonneg_right (mul_le_mul hcount hcharge (Real.exp_nonneg _) (by positivity)) hprod
    _ = _ := by
      have hc : K^(2*k) * Real.exp (g*(1+4*margin/cutoff))^k =
          ((Q*C^2*256^g)^2 * Real.exp (g*(1+4*margin/cutoff)))^k := by
        rw [pow_mul, ← mul_pow]
      apply congrArg₂ (fun a b : ℝ => a*b) hc
      dsimp only [L, ratio]
      exact htel


#print axioms actual_forest_arm_product
#print axioms recorded_edge_card_le
end ExceptionalTimes.GenericForestArmWeights


