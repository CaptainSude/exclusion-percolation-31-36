import ExceptionalTimes.ExpansionLimit

/-! Convergence for growing finite weighted sums by separating a uniformly
controlled good set from a uniformly negligible bad set. -/
open Filter
open scoped Classical BigOperators Topology
namespace ExceptionalTimes.MovingWeightedLimit
noncomputable section

variable {I : Type*} [Fintype I]

theorem weighted_sum_bound (w f g : I→ℝ) (bad : Finset I)
    (hw : ∀ i,0≤w i) {η : ℝ} (hη : 0≤η)
    (hgood : ∀ i,i∉bad → |f i-g i|≤η) :
    |∑ i,w i*(f i-g i)|≤
      (∑ i∈bad,w i*(|f i|+|g i|))+η*(∑ i,w i) := by
  calc
    _ ≤ ∑ i,|w i*(f i-g i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i,w i*|f i-g i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul,abs_of_nonneg (hw i)]
    _ ≤ ∑ i,((if i∈bad then w i*(|f i|+|g i|) else 0)+w i*η) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i∈bad
      · rw [ite_eq_left hi]
        exact (mul_le_mul_of_nonneg_left (abs_sub _ _) (hw i)).trans
          (le_add_of_nonneg_right (mul_nonneg (hw i) hη))
      · rw [ite_eq_right hi,zero_add]
        exact mul_le_mul_of_nonneg_left (hgood i hi) (hw i)
    _ = _ := by simp [Finset.sum_add_distrib,←Finset.mul_sum,mul_comm]

variable {Is : ℕ→Type*} [∀ n,Fintype (Is n)]

/-- The bad sets may depend on both the tolerance parameter and mesh;
the index types and weights may also change with the mesh. -/
theorem tendsto_weighted_difference (w f g : ∀ n,Is n→ℝ)
    (bad : ℝ→∀ n,Finset (Is n)) (C : ℝ)
    (hw : ∀ᶠ n in atTop,∀ i,0≤w n i)
    (hmass : ∀ᶠ n in atTop,∑ i,w n i≤C)
    (hgood : ∀ δ : ℝ,0<δ → ∀ η : ℝ,0<η →
      ∀ᶠ n in atTop,∀ i,i∉bad δ n → |f n i-g n i|<η)
    (hbad : ∀ η : ℝ,0<η → ∃ δ : ℝ,0<δ ∧
      ∀ᶠ n in atTop,(∑ i∈bad δ n,w n i*(|f n i|+|g n i|))<η) :
    Tendsto (fun n => ∑ i,w n i*(f n i-g n i)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := hbad (ε/2) (by positivity)
  let η := ε/(2*(|C|+1))
  have hη : 0<η := by dsimp [η]; positivity
  have hsmall : η*C<ε/2 := by
    have hc : C < |C|+1 := lt_add_of_le_of_pos (le_abs_self C) (by norm_num)
    have h := mul_lt_mul_of_pos_left hc hη
    have he : η*(|C|+1)=ε/2 := by
      dsimp [η]
      have hc0 : |C|+1≠0 := by positivity
      field_simp
    linarith
  filter_upwards [hw,hmass,hgood δ hδ η hη,hb] with n hwn hmn hgn hbn
  rw [Real.dist_eq,sub_zero]
  have h := weighted_sum_bound (w n) (f n) (g n) (bad δ n) hwn hη.le
    (fun i hi => (hgn i hi).le)
  have hm := mul_le_mul_of_nonneg_left hmn hη.le
  linarith

#print axioms tendsto_weighted_difference
end
end ExceptionalTimes.MovingWeightedLimit
