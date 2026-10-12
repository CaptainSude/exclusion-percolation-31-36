import ExceptionalTimes.ForestBridge

/-! Actual independent probe probabilities followed by actual leaf integration.
The remaining geometric inputs are local arm necessity and the assignment of
one-probe arm bounds to the explicitly recorded leaf factors. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ProbeForestIntegration

open EnvironmentVariance CenteredBlocks ProbeProduct ForestIntegration ForestBridge ForestCounting

variable {n : ℕ} {R X P I T Q Z : Type*}
variable [Fintype X] [Fintype I] [Fintype T] [DecidableEq T] [Fintype Z]
variable {Ξ : Fin n → Type*} [∀ i, Fintype (Ξ i)]
variable {Choices : Fin n → Type*} [∀ i, Fintype (Choices i)]

/-- Local static arm bounds are multiplied under the normalized independent
probe law and then integrated along the recorded forest. The tested outer
functional may have either sign and need not be monotone. -/
theorem centered_probe_forest_integral
    (F : LeafOrder R n) (position : X → P) (root : R → P)
    (μ : Fin n → X → ℝ) (K : Fin n → X → P → ℝ)
    (ν₀ : FiniteLaw Z) (ν : ∀ i, FiniteLaw (Ξ i))
    (w : I → (T → PairColor) → ℝ)
    (cross : (Fin n → X) → (Z × (∀ i, Ξ i)) → Q → T → (I → PairColor) → Bool)
    (outer : (Fin n → X) → (Z × (∀ i, Ξ i)) → (Q × T → Bool) → ℝ)
    (Arm : (Fin n → X) → ∀ i, Choices i → Ξ i → Prop)
    (α : (Fin n → X) → ∀ i, Choices i → ℝ)
    (hw : ∀ i, ∑ h, w i h = 0)
    (hf : ∀ x o h, |outer x o (historyTests (cross x o) h)| ≤ 1)
    (hnecessary : ∀ x o, AllEndpointPivotal (cross x o) →
      ∀ i, ∃ c, Arm x i c (o.2 i))
    (hstatic : ∀ x i c, probability (ν i) (Arm x i c) ≤ α x i c)
    (hfactor : ∀ x i, ∑ c, α x i c ≤ F.factors position root K x i)
    (M C : ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hK : ∀ i a y, 0 ≤ K i a y)
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C) (hM : ∀ i, ∑ a, μ i a ≤ M)
    (hC : ∀ i y, ∑ a, μ i a * K i a y ≤ C) :
    (∑ x : Fin n → X, (∏ i, μ i (x i)) *
      |(probeLaw ν₀ ν).expect (fun o => kernel w
        (fun h => outer x o (historyTests (cross x o) h)))|) ≤
      (∏ i, variation (w i)) * (C ^ F.edgeCount * M ^ F.freeCount) := by
  have hvar : 0 ≤ ∏ i, variation (w i) :=
    Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun h _ => abs_nonneg (w i h)))
  have hα (x) (i) (c) : 0 ≤ α x i c :=
    (probability_nonneg (ν i) (Arm x i c)).trans (hstatic x i c)
  calc
    _ ≤ ∑ x : Fin n → X, (∏ i, μ i (x i)) *
        ((∏ i, variation (w i)) * ∏ i, F.factors position root K x i) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => hμ i _))
      apply (centered_arm_product_bound ν₀ ν w (cross x) (outer x) (Arm x) (α x)
        hw (hf x) (hnecessary x) (hstatic x)).trans
      apply mul_le_mul_of_nonneg_left _ hvar
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun c _ => hα x i c)
      · intro i _
        exact hfactor x i
    _ = (∏ i, variation (w i)) * integral F position root μ K := by
      unfold integral
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_le_uniform F position root μ K M C hμ hK hM0 hC0 hM hC) hvar

#print axioms centered_probe_forest_integral

end ExceptionalTimes.ProbeForestIntegration
