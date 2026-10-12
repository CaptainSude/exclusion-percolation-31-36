import ExceptionalTimes.ForestLatticeProduct

/-! The unordered radial integral summed over the actual finite family of all
eligible rooted forests, with its combinatorial count included. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestLatticeFamily

open ForestIntegration ForestCounting ForestEdgeProduct ForestArmRadial ForestLatticeProduct
open LatticeRadial LatticeForest RootKruskal ForestLifeGeometry

noncomputable def eligibleForests {N : ℕ} (fixed : Fin N → Prop) : Finset (SimpleGraph (Fin N)) :=
  Finset.univ.filter (fun G => G.IsAcyclic ∧ RootsSeparated G fixed)

theorem mem_eligibleForests {N : ℕ} (fixed : Fin N → Prop) (G : SimpleGraph (Fin N)) :
    G ∈ eligibleForests fixed ↔ G.IsAcyclic ∧ RootsSeparated G fixed := by
  simp [eligibleForests]

theorem kruskal_mem_eligible {N : ℕ} {X : Type*} [PseudoMetricSpace X]
    (fixed : Fin N → Prop) (position : Fin N → X) (cutoff stop : ℝ) :
    recorded fixed position cutoff ⊓ threshold position cutoff stop ∈ eligibleForests fixed := by
  rw [mem_eligibleForests]
  constructor
  · exact SimpleGraph.IsAcyclic.anti inf_le_left (greedy_isAcyclic fixed _)
  · intro u v hu hv hreach
    exact greedy_rootsSeparated fixed _ u v hu hv (hreach.mono inf_le_left)

noncomputable def radialIntegral {N : ℕ} {A : Type*} [Fintype A]
    (G : SimpleGraph (Fin N)) (fixed : Fin N → Prop)
    (position : A → ℂ) (root : {v // fixed v} → ℂ)
    (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v)
    (μ : Fin L.length → A → ℝ) (b g R : ℝ) : ℝ :=
  ∑ x : Fin L.length → A, (∏ i, μ i (x i)) *
    ∏ e ∈ G.edgeFinset, radialEdge
      (configuredPosition fixed position root L hL hmem x) b g R e

theorem radialIntegral_eq_graphIntegral {N : ℕ} {A : Type*} [Fintype A]
    (G : SimpleGraph (Fin N)) (fixed : Fin N → Prop)
    (position : A → ℂ) (root : {v // fixed v} → ℂ) (hroot : RootsSeparated G fixed)
    (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v)
    (μ : Fin L.length → A → ℝ) {b g R : ℝ} (hb : 0 ≤ b) :
    radialIntegral G fixed position root L hL hmem μ b g R =
      graphIntegral G fixed position root L μ
        (fun _ a y => clippedKernel ‖position a-y‖ b g R) := by
  unfold radialIntegral graphIntegral
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact (graphProduct_eq_radial G fixed position root (roots_not_adj G fixed hroot) L hL hmem hb x).symm

set_option maxHeartbeats 800000 in
/-- Every eligible graph is included, with exactly k variable positions and
the proved binomial forest count. Each summand is the literal Sym2 edge product. -/
theorem all_forests_lattice_integral (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v} = J)
    (s : Finset Site) {ε b c g R r₀ : ℝ} (center : ℂ)
    (hε : 0 < ε) (hc : 0 < c) (hb : c*ε ≤ b) (hg : 0 ≤ g) (hg2 : g < 2)
    (hR : 0 < R) (hr₀ : ε ≤ r₀)
    (hs : ∀ v ∈ s, ‖scaledEmbedding ε v-center‖ ≤ r₀)
    (root : {v // fixed v} → ℂ) :
    ∃ (L : eligibleForests fixed → List (Fin (k+J))) (hL : ∀ G, (L G).Nodup)
      (hmem : ∀ G v, v ∈ L G ↔ ¬ fixed v),
      (∀ G, (L G).length = k) ∧
      (∑ G : eligibleForests fixed, radialIntegral G.val fixed
        (fun v : s => scaledEmbedding ε v) root (L G) (hL G) (hmem G)
        (fun _ _ => ε^2) b g R) ≤
      ∑ j ∈ Finset.range (k+1), (((k+J)^2).choose j : ℝ) *
        ((radialConstant g + 121/c^2)*R^(2-g))^j * (121*r₀^2)^(k-j) := by
  have hf : ∀ G ∈ eligibleForests fixed, G.IsAcyclic ∧ RootsSeparated G fixed :=
    fun G hG => (mem_eligibleForests fixed G).mp hG
  obtain ⟨L₀, h₀, hbound⟩ := lattice_forest_family_integral k J (eligibleForests fixed)
    fixed hrootsize hf s center hε hc hb hg hg2 hR hr₀ hs root
  let L := fun G : eligibleForests fixed => L₀ G.val
  let hL := fun G : eligibleForests fixed => (h₀ G.val G.property).1
  let hmem := fun G : eligibleForests fixed => (h₀ G.val G.property).2.1
  refine ⟨L, hL, hmem, fun G => (h₀ G.val G.property).2.2, ?_⟩
  have hb0 : 0 ≤ b := (mul_pos hc hε).le.trans hb
  calc
    _ = ∑ G : eligibleForests fixed, graphIntegral G.val fixed
        (fun v : s => scaledEmbedding ε v) root (L₀ G.val)
        (fun _ _ => ε^2) (fun _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R) := by
      apply Finset.sum_congr rfl
      intro G _
      exact radialIntegral_eq_graphIntegral G.val fixed _ root (hf G.val G.property).2
        (L G) (hL G) (hmem G) _ hb0
    _ = ∑ G ∈ eligibleForests fixed, graphIntegral G fixed
        (fun v : s => scaledEmbedding ε v) root (L₀ G)
        (fun _ _ => ε^2) (fun _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R) :=
      Finset.sum_coe_sort (eligibleForests fixed) (fun G => graphIntegral G fixed
        (fun v : s => scaledEmbedding ε v) root (L₀ G)
        (fun _ _ => ε^2) (fun _ v y => clippedKernel ‖scaledEmbedding ε v-y‖ b g R))
    _ ≤ _ := hbound

#print axioms kruskal_mem_eligible
#print axioms all_forests_lattice_integral

end ExceptionalTimes.ForestLatticeFamily
