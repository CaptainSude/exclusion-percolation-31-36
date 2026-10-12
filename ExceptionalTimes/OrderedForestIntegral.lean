import ExceptionalTimes.RootedAnchorLabels
import ExceptionalTimes.ForestCoefficientIntegral

/-! The common counted forest family for ordered insertion anchors. This
is the precise relabelling dictionary between actual selected forests and
the weighted lattice integral with its factorial gain. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.OrderedForestIntegral

open PairSquareSewing ForestRelabel RootedAnchorLabels ForestIntegration
open ForestLatticeFamily ForestCounting ForestArmRadial ForestCharge
open ForestAnchorIntegration ForestCoefficientIntegral LatticeRadial

variable {I J X : Type*} [Fintype I] [Fintype J] [PseudoMetricSpace X]

theorem ordered_graph_bound {k : ℕ} (order : Fin k ≃ I)
    (G : SimpleGraph (I⊕J)) (hG : G.IsAcyclic) (hroots : RootsSeparated G selectedRoot)
    (position : I → X) (root : J → X) (b g R w : ℝ) (hw : 0≤w) :
    graphWeight G (Sum.elim position root) b g R w≤
      ∑ H∈eligibleForests (fixed k J),
        graphWeight H (anchorPosition k id root (fun i => position (order i))) b g R w := by
  have h := graph_le_all_forests (orderedLabels (J := J) order) selectedRoot G hG hroots
    (Sum.elim position root) b g R w hw
  have he : (fun v => selectedRoot ((orderedLabels (J := J) order).symm v))=fixed k J :=
    funext (fun v => propext (orderedLabels_fixed order v))
  rw [he,orderedPosition_eq] at h
  exact h

theorem graphWeight_eq_forward {N : ℕ} (G : SimpleGraph (Fin N))
    (position : Fin N → X) (b g R w : ℝ) :
    graphWeight G position b g R w=
      w^(forwardEdges G).card*∏ e∈G.edgeFinset,radialEdge position b g R e := by
  unfold graphWeight
  apply congrArg₂ (fun x y : ℝ => x*y)
  · apply congrArg (fun n : ℕ => w^n)
    convert card_edgeFinset_eq_forwardEdges G using 1
  · apply Finset.prod_congr (by ext a; simp only [SimpleGraph.mem_edgeFinset])
    intro a _
    rfl

theorem ordered_lattice_forest_bound (k : ℕ) (hk : 1≤k)
    (s : Finset Site) {ε b c g R r₀ A d D : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hR : 0<R) (hr₀ : ε≤r₀) (hA : 0≤A) (hd : 0<d)
    (hlower : d*(k:ℝ)^(-(1/2:ℝ))≤R)
    (hupper : R≤D*(k:ℝ)^(-(1/2:ℝ)))
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀) (root : J → ℂ) :
    R^(-g*(k:ℝ))/(k.factorial:ℝ)*
      (ε^(2*k)*(∑ x : Fin k → s,∑ H∈eligibleForests (fixed k J),
        graphWeight H (anchorPosition k (fun v : s => scaledEmbedding ε v) root x)
          b g R (A*R^g)))≤
      (summationConstant (Fintype.card J) d D A c g r₀)^k*(k:ℝ)^(-(1-g/2)*k) := by
  rw [sum_anchorPosition k (fun v : s => scaledEmbedding ε v) root
    (fun p => ∑ H∈eligibleForests (fixed k J),graphWeight H p b g R (A*R^g))]
  have hsum (x : {v // ¬fixed k J v} → s) :
      (∑ H∈eligibleForests (fixed k J),graphWeight H
        (assignedPosition (fixed k J) (fun v : s => scaledEmbedding ε v)
          (fun v => root (roots k J v)) x) b g R (A*R^g))=
      ∑ H : eligibleForests (fixed k J),(A*R^g)^(forwardEdges H.val).card*
        ∏ e∈H.val.edgeFinset,radialEdge
          (assignedPosition (fixed k J) (fun v : s => scaledEmbedding ε v)
            (fun v => root (roots k J v)) x) b g R e := by
    simp_rw [graphWeight_eq_forward]
    exact (Finset.sum_coe_sort _ _).symm
  simp_rw [hsum]
  exact counted_lattice_forest_bound k (Fintype.card J) hk (fixed k J) (roots_card k)
    s center hε hc hb hg hg2 hR hr₀ hA hd hlower hupper hs (fun v => root (roots k J v))

#print axioms ordered_graph_bound
#print axioms ordered_lattice_forest_bound

end ExceptionalTimes.OrderedForestIntegral
