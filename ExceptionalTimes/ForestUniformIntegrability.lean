import ExceptionalTimes.ForestWeightedAnchors
import Mathlib.Analysis.MeanInequalities

/-! A proved uniform-integrability bound for each literal radial forest
product. The higher moment is another already integrated forest kernel. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestUniformIntegrability

open ForestArmRadial ForestAnchorIntegration ForestLatticeFamily ForestWeightedAnchors
open LatticeRadial ForestCounting

variable {V X A : Type*} [PseudoMetricSpace X]

theorem radialEdge_rpow (position : V → X) (b g R p : ℝ) (hp : 0<p) (a : Sym2 V) :
    (radialEdge position b g R a)^p=radialEdge position b (g*p) R a := by
  unfold radialEdge
  split_ifs
  · rw [←Real.rpow_mul (ForestGeometry.clippedEdgeLength_nonneg _ _ _)]
    congr 1
    ring
  · exact Real.zero_rpow hp.ne'

theorem radial_product_rpow [Fintype V] (G : SimpleGraph V)
    (position : V → X) (b g R p : ℝ) (hp : 0<p) :
    (∏ a∈G.edgeFinset,radialEdge position b g R a)^p=
      ∏ a∈G.edgeFinset,radialEdge position b (g*p) R a := by
  rw [←Real.finsetProd_rpow _ _ (fun a _ => radialEdge_nonneg _ _ _ _ _) p]
  apply Finset.prod_congr rfl
  intro a _
  exact radialEdge_rpow position b g R p hp a

theorem holder_mass_factor {μ X Y p q : ℝ} (hμ : 0<μ) (hX : 0≤X) (hY : 0≤Y)
    (hpq : Real.HolderConjugate p q) :
    (μ*X)^(1/p)*(μ*Y)^(1/q)=μ*(X^(1/p)*Y^(1/q)) := by
  rw [Real.mul_rpow hμ.le hX,Real.mul_rpow hμ.le hY]
  calc
    _ = (μ^(1/p)*μ^(1/q))*(X^(1/p)*Y^(1/q)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hμ]
      have h : 1/p+1/q=(1:ℝ) := by simpa only [one_div] using hpq.inv_add_inv_eq_one
      rw [h,Real.rpow_one]

theorem restricted_holder [Fintype A] (bad : Finset A) (f : A → ℝ)
    (hf : ∀ a,0≤f a) {μ p q : ℝ} (hμ : 0<μ) (hpq : Real.HolderConjugate p q) :
    μ*(∑ a∈bad,f a)≤
      (μ*(bad.card:ℝ))^(1/q)*(μ*∑ a,f a^p)^(1/p) := by
  have hp : 0<p := hpq.pos
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg bad (f := f) (g := fun _ => 1) hpq
    (fun a _ => hf a) (fun _ _ => (by norm_num : (0:ℝ)≤1))
  simp only [mul_one,Real.one_rpow,Finset.sum_const,nsmul_eq_mul,mul_one] at h
  have hs : (∑ a∈bad,f a^p)≤∑ a,f a^p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => Real.rpow_nonneg (hf a) p)
  have hnorm := Real.rpow_le_rpow (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (hf a) p))
    hs (by positivity : 0≤1/p)
  have h' := h.trans (mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hm := mul_le_mul_of_nonneg_left h' hμ.le
  rw [←holder_mass_factor hμ (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (hf a) p))
    (Nat.cast_nonneg bad.card) hpq] at hm
  simpa only [mul_comm] using hm

theorem forest_bad_mass_bound (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v}=J) (G : eligibleForests fixed)
    (s : Finset Site) (bad : Finset ({v // ¬fixed v} → s))
    {ε b c g R r₀ p q : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g)
    (hpq : Real.HolderConjugate p q) (hgp : g*p<2)
    (hR : 0<R) (hr₀ : ε≤r₀)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀)
    (root : {v // fixed v} → ℂ) :
    ε^(2*k)*(∑ x∈bad, ∏ e∈G.val.edgeFinset,
      radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)≤
      (ε^(2*k)*(bad.card:ℝ))^(1/q)*
        (((radialConstant (g*p)+121/c^2)*R^(2-g*p))^(forwardEdges G.val).card*
          (121*r₀^2)^(k-(forwardEdges G.val).card))^(1/p) := by
  have hp : 0<p := hpq.pos
  have h := restricted_holder bad
    (fun x => ∏ e∈G.val.edgeFinset,
      radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)
    (fun x => Finset.prod_nonneg (fun e _ => radialEdge_nonneg _ _ _ _ _))
    (pow_pos hε (2*k)) hpq
  simp_rw [radial_product_rpow _ _ b g R p hp] at h
  have hm := forest_anchor_integral k J fixed hrootsize G s center hε hc hb
    (mul_nonneg hg hp.le) hgp hR hr₀ hs root
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (mul_nonneg (pow_nonneg hε.le _)
      (Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun e _ =>
        radialEdge_nonneg _ _ _ _ _)))) hm (by positivity : 0≤1/p))
    (Real.rpow_nonneg (mul_nonneg (pow_nonneg hε.le _) (Nat.cast_nonneg _)) _))

#print axioms forest_bad_mass_bound

end ExceptionalTimes.ForestUniformIntegrability




