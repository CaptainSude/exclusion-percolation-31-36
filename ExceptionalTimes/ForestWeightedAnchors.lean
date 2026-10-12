import ExceptionalTimes.ForestAnchorIntegration

/-! Edge-count weights are retained in the actual anchor sum. This
preserves the radius gain needed when the forest stop is of order k^(-1/2). -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestWeightedAnchors

open ForestAnchorIntegration ForestIntegration ForestEdgeProduct ForestLatticeFamily
open ForestArmRadial LatticeRadial LatticeForest ForestCounting ForestBridge ForestLatticeProduct

theorem eligible_edge_card_le (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v}=J) (G : eligibleForests fixed) :
    (forwardEdges G.val).card≤k := by
  have hg := (mem_eligibleForests fixed G.val).mp G.property
  obtain ⟨L,F,hL,hmem,hF⟩ := exists_graph_encoding G.val hg.1 fixed hg.2
  have hlen : L.length=k := by
    have h := Fintype.card_congr (freeLabels fixed L hL hmem)
    rw [Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_fin,hrootsize] at h
    omega
  rw [←graphEdgeCount_eq_forwardEdges G.val fixed hg.2 L hL hmem,
    encoded_edgeCount G.val fixed L F hF]
  exact (Nat.le_add_right F.edgeCount F.freeCount).trans_eq (F.counts.trans hlen)

theorem forest_anchor_integral (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v}=J) (G : eligibleForests fixed)
    (s : Finset Site) {ε b c g R r₀ : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hR : 0<R) (hr₀ : ε≤r₀)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀)
    (root : {v // fixed v} → ℂ) :
    ε^(2*k)*(∑ x : {v // ¬fixed v} → s, ∏ e∈G.val.edgeFinset,
      radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)≤
      ((radialConstant g+121/c^2)*R^(2-g))^(forwardEdges G.val).card*
        (121*r₀^2)^(k-(forwardEdges G.val).card) := by
  have hfree : Fintype.card {v // ¬fixed v}=k := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,hrootsize]
    omega
  have hg' := (mem_eligibleForests fixed G.val).mp G.property
  obtain ⟨L,hL,hmem,hbound⟩ := lattice_edge_product_integral G.val fixed hg'.1 hg'.2 s center
    hε hc hb hg hg2 hR hr₀ hs root
  have hlen : L.length=k := by
    simpa only [Fintype.card_fin,hfree] using Fintype.card_congr (freeLabels fixed L hL hmem)
  change radialIntegral G.val fixed (fun v : s => scaledEmbedding ε v) root L hL hmem
    (fun _ _ => ε^2) b g R≤_ at hbound
  rw [radialIntegral_eq_anchorSum,hfree,←pow_mul,hlen] at hbound
  exact hbound

set_option maxHeartbeats 800000 in
theorem weighted_forests_anchor_sum (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v}=J)
    (s : Finset Site) {ε b c g R r₀ w : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hR : 0<R) (hr₀ : ε≤r₀) (hw : 0≤w)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀)
    (root : {v // fixed v} → ℂ) :
    ε^(2*k)*(∑ x : {v // ¬fixed v} → s, ∑ G : eligibleForests fixed,
      w^(forwardEdges G.val).card*∏ e∈G.val.edgeFinset,
        radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)≤
      ∑ j∈Finset.range (k+1),(((k+J)^2).choose j : ℝ)*
        (w*(radialConstant g+121/c^2)*R^(2-g))^j*(121*r₀^2)^(k-j) := by
  let C := (radialConstant g+121/c^2)*R^(2-g)
  let M := 121*r₀^2
  have hC : 0≤C := mul_nonneg (add_nonneg (radialConstant_nonneg hg2) (by positivity))
    (Real.rpow_nonneg hR.le _)
  have hM : 0≤M := by dsimp [M]; positivity
  calc
    _ = ∑ G : eligibleForests fixed,w^(forwardEdges G.val).card*
        (ε^(2*k)*(∑ x : {v // ¬fixed v} → s, ∏ e∈G.val.edgeFinset,
          radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)) := by
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G _
      rw [←Finset.mul_sum]
      ring
    _ ≤ ∑ G : eligibleForests fixed,w^(forwardEdges G.val).card*
        (C^(forwardEdges G.val).card*M^(k-(forwardEdges G.val).card)) := by
      apply Finset.sum_le_sum
      intro G _
      exact mul_le_mul_of_nonneg_left
        (forest_anchor_integral k J fixed hrootsize G s center hε hc hb hg hg2 hR hr₀ hs root)
        (pow_nonneg hw _)
    _ = ∑ G∈eligibleForests fixed,(w*C)^(forwardEdges G).card*M^(k-(forwardEdges G).card) := by
      simpa only [mul_pow,mul_assoc] using Finset.sum_coe_sort (eligibleForests fixed)
        (fun G => (w*C)^(forwardEdges G).card*M^(k-(forwardEdges G).card))
    _ ≤ ∑ j∈Finset.range (k+1),(((k+J)^2).choose j : ℝ)*((w*C)^j*M^(k-j)) :=
      family_sum_le (eligibleForests fixed) (fun j => (w*C)^j*M^(k-j))
        (fun j => mul_nonneg (pow_nonneg (mul_nonneg hw hC) j) (pow_nonneg hM _))
        (fun G hG => eligible_edge_card_le k J fixed hrootsize ⟨G,hG⟩)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [C,M]
      rw [mul_assoc w (radialConstant g+121/c^2)]
      ring

#print axioms weighted_forests_anchor_sum

end ExceptionalTimes.ForestWeightedAnchors

