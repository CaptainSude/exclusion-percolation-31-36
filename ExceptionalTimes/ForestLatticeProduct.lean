import ExceptionalTimes.ForestEdgeProduct
import ExceptionalTimes.LatticeForest

/-! Literal unordered radial edge products under lattice counting measure,
connected exactly to the proved forest leaf integration. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestLatticeProduct

open ForestIntegration ForestCounting ForestEdgeProduct ForestArmRadial LatticeRadial LatticeForest

theorem graphProduct_eq_radial {N : ℕ} {A : Type*} (G : SimpleGraph (Fin N)) (fixed : Fin N → Prop)
    (position : A → ℂ) (root : {v // fixed v} → ℂ)
    (hroots : ∀ u v, fixed u → fixed v → ¬ G.Adj u v)
    (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v)
    {b g R : ℝ} (hb : 0 ≤ b) (x : Fin L.length → A) :
    graphProduct G fixed position root L
      (fun _ a y => clippedKernel ‖position a-y‖ b g R) x =
      ∏ e ∈ G.edgeFinset,
        radialEdge (configuredPosition fixed position root L hL hmem x) b g R e := by
  rw [graphProduct_eq_edges G fixed position root hroots L hL hmem
    (fun a y => clippedKernel ‖a-y‖ b g R)
    (fun a y => by rw [norm_sub_rev a y])
    (fun a y => clippedKernel_nonneg _ _ _ _ hb) x]
  apply Finset.prod_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ u v =>
    change clippedKernel ‖_ - _‖ b g R = _
    rw [radialEdge_mk, dist_eq_norm]

/-- The integral now literally sums the unordered radial product that appears
in the centered forest estimate. The elimination list is constructed. -/
theorem lattice_edge_product_integral {N : ℕ} (G : SimpleGraph (Fin N))
    (fixed : Fin N → Prop) (hG : G.IsAcyclic) (hroot : RootsSeparated G fixed)
    (s : Finset Site) {ε b c g R r₀ : ℝ} (center : ℂ)
    (hε : 0 < ε) (hc : 0 < c) (hb : c*ε ≤ b) (hg : 0 ≤ g) (hg2 : g < 2)
    (hR : 0 < R) (hr₀ : ε ≤ r₀)
    (hs : ∀ v ∈ s, ‖scaledEmbedding ε v-center‖ ≤ r₀)
    (root : {v // fixed v} → ℂ) :
    ∃ (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v),
      (∑ x : Fin L.length → s, (∏ _i : Fin L.length, ε^2) *
        ∏ e ∈ G.edgeFinset, radialEdge
          (configuredPosition fixed (fun v : s => scaledEmbedding ε v) root L hL hmem x) b g R e) ≤
      ((radialConstant g + 121/c^2) * R^(2-g)) ^ (forwardEdges G).card *
        (121*r₀^2) ^ (L.length-(forwardEdges G).card) := by
  obtain ⟨L, hL, hmem, hbound⟩ := lattice_forest_integral G fixed hG hroot s center
    hε hc hb hg hg2 hR hr₀ hs root
  refine ⟨L, hL, hmem, ?_⟩
  have hb0 : 0 ≤ b := (mul_pos hc hε).le.trans hb
  have heq : (∑ x : Fin L.length → s, (∏ _i : Fin L.length, ε^2) *
      ∏ e ∈ G.edgeFinset, radialEdge
        (configuredPosition fixed (fun v : s => scaledEmbedding ε v) root L hL hmem x) b g R e) =
      graphIntegral G fixed (fun v : s => scaledEmbedding ε v) root L
        (fun _ _ => ε^2) (fun _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R) := by
    unfold graphIntegral
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    exact (graphProduct_eq_radial G fixed (fun v : s => scaledEmbedding ε v) root
      (roots_not_adj G fixed hroot) L hL hmem hb0 x).symm
  exact heq.trans_le hbound

#print axioms graphProduct_eq_radial
#print axioms lattice_edge_product_integral

end ExceptionalTimes.ForestLatticeProduct
