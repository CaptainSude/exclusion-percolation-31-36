import ExceptionalTimes.ForestBridge
import ExceptionalTimes.LatticeRadial

/-! The actual triangular-lattice radial bound inserted into finite rooted
forest integration and graph enumeration. All variable positions are summed
against scaled lattice counting measure; roots may lie anywhere in the plane. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.LatticeForest

open ForestIntegration ForestCounting ForestBridge LatticeRadial

theorem radialConstant_nonneg {g : ℝ} (hg : g < 2) : 0 ≤ radialConstant g := by
  unfold radialConstant
  exact div_nonneg (by positivity) (sub_nonneg.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith : 0 < 2-g)).le)

theorem subtype_clipped_sum (s : Finset Site) (ε b g R : ℝ) (y : ℂ) :
    (∑ v : s, ε^2 * clippedKernel ‖scaledEmbedding ε v-y‖ b g R) =
      clippedSum s ε b g R y := by
  rw [← Finset.mul_sum]
  unfold clippedSum
  congr 1
  exact Finset.sum_coe_sort s (fun v : Site => clippedKernel ‖scaledEmbedding ε v-y‖ b g R)

theorem subtype_mass (s : Finset Site) (ε : ℝ) :
    (∑ _v : s, ε^2) = ε^2 * (s.card : ℝ) := by
  simp [mul_comm]

/-- An actual finite rooted forest admits an order in which its literal
clipped radial product satisfies the count-exact integral bound. -/
theorem lattice_forest_integral {N : ℕ} (G : SimpleGraph (Fin N))
    (fixed : Fin N → Prop) (hG : G.IsAcyclic) (hroot : RootsSeparated G fixed)
    (s : Finset Site) {ε b c g R r₀ : ℝ} (center : ℂ)
    (hε : 0 < ε) (hc : 0 < c) (hb : c*ε ≤ b) (hg : 0 ≤ g) (hg2 : g < 2)
    (hR : 0 < R) (hr₀ : ε ≤ r₀)
    (hs : ∀ v ∈ s, ‖scaledEmbedding ε v-center‖ ≤ r₀)
    (root : {v // fixed v} → ℂ) :
    ∃ L : List (Fin N), L.Nodup ∧ (∀ v, v ∈ L ↔ ¬ fixed v) ∧
      graphIntegral G fixed (fun v : s => scaledEmbedding ε v) root L
        (fun _ _ => ε^2) (fun _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R) ≤
      ((radialConstant g + 121/c^2) * R^(2-g)) ^ (forwardEdges G).card *
        (121*r₀^2) ^ (L.length-(forwardEdges G).card) := by
  obtain ⟨L, F, hL, hmem, hF⟩ := exists_graph_encoding G hG fixed hroot
  refine ⟨L, hL, hmem, ?_⟩
  have hb0 : 0 ≤ b := (mul_pos hc hε).le.trans hb
  have h := graphIntegral_le_count G fixed (fun v : s => scaledEmbedding ε v) root L F hF
    (fun _ _ => ε^2) (fun _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R)
    (121*r₀^2) ((radialConstant g + 121/c^2)*R^(2-g))
    (fun _ _ => sq_nonneg ε) (fun _ _ _ => clippedKernel_nonneg _ _ _ _ hb0)
    (by positivity) (mul_nonneg (add_nonneg (radialConstant_nonneg hg2) (by positivity))
      (Real.rpow_nonneg hR.le _))
    (fun _ => by rw [subtype_mass]; exact scaled_ball_mass_le s hε hr₀ center hs)
    (fun _ y => by rw [subtype_clipped_sum]; exact clippedSum_le_of_clip_ratio s y hε hc hb hg hg2 hR)
  simpa only [graphEdgeCount_eq_forwardEdges G fixed hroot L hL hmem] using h

set_option maxHeartbeats 800000 in
/-- Both the one-edge integrals and the number of eligible forests are included.
The leaf orders are constructed from acyclicity, and have exactly `k` variables. -/
theorem lattice_forest_family_integral (k J : ℕ)
    (family : Finset (SimpleGraph (Fin (k+J)))) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v} = J)
    (hgraph : ∀ G ∈ family, G.IsAcyclic ∧ RootsSeparated G fixed)
    (s : Finset Site) {ε b c g R r₀ : ℝ} (center : ℂ)
    (hε : 0 < ε) (hc : 0 < c) (hb : c*ε ≤ b) (hg : 0 ≤ g) (hg2 : g < 2)
    (hR : 0 < R) (hr₀ : ε ≤ r₀)
    (hs : ∀ v ∈ s, ‖scaledEmbedding ε v-center‖ ≤ r₀)
    (root : {v // fixed v} → ℂ) :
    ∃ L : SimpleGraph (Fin (k+J)) → List (Fin (k+J)),
      (∀ G ∈ family, (L G).Nodup ∧ (∀ v, v ∈ L G ↔ ¬ fixed v) ∧ (L G).length = k) ∧
      (∑ G ∈ family, graphIntegral G fixed (fun v : s => scaledEmbedding ε v) root (L G)
        (fun _ _ => ε^2) (fun _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R)) ≤
      ∑ j ∈ Finset.range (k+1), (((k+J)^2).choose j : ℝ) *
        ((radialConstant g + 121/c^2)*R^(2-g)) ^ j * (121*r₀^2) ^ (k-j) := by
  classical
  have hex (G : SimpleGraph (Fin (k+J))) : ∃ L : List (Fin (k+J)), G ∈ family →
      L.Nodup ∧ (∀ v, v ∈ L ↔ ¬ fixed v) ∧ Eliminates G fixed L := by
    by_cases hG : G ∈ family
    · obtain ⟨L, hL, hmem, hElim⟩ := exists_complete_elimination_list G (hgraph G hG).1
        fixed (hgraph G hG).2
      exact ⟨L, fun _ => ⟨hL, hmem, hElim⟩⟩
    · exact ⟨[], fun h => False.elim (hG h)⟩
  choose L hL using hex
  have hlen (G) (hG : G ∈ family) : (L G).length = k := by
    have hh := Fintype.card_congr (endpointEquiv fixed (L G) (hL G hG).1 (hL G hG).2.1)
    simp only [Fintype.card_sum, Fintype.card_fin, hrootsize] at hh
    omega
  refine ⟨L, fun G hG => ⟨(hL G hG).1, (hL G hG).2.1, hlen G hG⟩, ?_⟩
  have hb0 : 0 ≤ b := (mul_pos hc hε).le.trans hb
  exact forest_family_integral_le family fixed L hgraph hL hlen
    (fun v : s => scaledEmbedding ε v) root (fun _ _ _ => ε^2)
    (fun _ _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R)
    (121*r₀^2) ((radialConstant g + 121/c^2)*R^(2-g)) (by positivity)
    (mul_nonneg (add_nonneg (radialConstant_nonneg hg2) (by positivity))
      (Real.rpow_nonneg hR.le _))
    (fun _ _ _ _ => sq_nonneg ε) (fun _ _ _ _ _ => clippedKernel_nonneg _ _ _ _ hb0)
    (fun _ _ _ => by rw [subtype_mass]; exact scaled_ball_mass_le s hε hr₀ center hs)
    (fun _ _ _ y => by rw [subtype_clipped_sum]; exact clippedSum_le_of_clip_ratio s y hε hc hb hg hg2 hR)

#print axioms lattice_forest_integral
#print axioms lattice_forest_family_integral

end ExceptionalTimes.LatticeForest
