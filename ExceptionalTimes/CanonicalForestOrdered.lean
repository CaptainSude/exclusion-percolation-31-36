import ExceptionalTimes.NormalizedForestProfile
import ExceptionalTimes.OrderedForestIntegral

/-! The actual recorded dimer forest is bounded by the single common
counted family used in the lattice coefficient integral. The profile is
renormalized at the chosen degree-dependent stop, with the radius factors
and the original global cutoff probability retained exactly. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.CanonicalForestOrdered

open PairSquareSewing RootKruskal ForestLifeGeometry ForestRelabel RootedAnchorLabels
open ForestLatticeFamily OrderedForestIntegral NormalizedForestProfile ForestIntegration

variable {I J : Type*} [Fintype I] [Fintype J]
noncomputable local instance : DecidableEq (I⊕J) := Classical.decEq _

noncomputable def prefactor (G : DimerGeometry I J) (cutoff stop C K g : ℝ) : ℝ :=
  ((K*C^2*256^g)^2*Real.exp (g*(1+4*G.margin/cutoff)))*(C*stop^g)

theorem actual_forest_ordered_bound {k : ℕ} (order : Fin k ≃ I)
    (G : DimerGeometry I J) {cutoff R stop C K g : ℝ}
    (hcut : 0<cutoff) (hcutR : cutoff≤R) (hRs : R≤stop) (hC : 0≤C)
    (p : ℝ → ℝ) (hpstop : p stop=1)
    (hp : ∀ t,0<t → t≤stop → 0<p t)
    (hlower : ∀ a b,0<a → a≤b → b≤stop → p b≤C*(b/a)^g*p a) :
    canonicalForestValue G cutoff R C K g (normalized p R)≤
      prefactor G cutoff stop C K g^k*p cutoff^k*R^(-g*(k:ℝ))*
        ∑ H∈eligibleForests (fixed k J),
          graphWeight H (anchorPosition k id G.root
            (fun i => position G.mesh (G.endpoint (order i,0)))) cutoff g R (C*R^g) := by
  have hR : 0<R := hcut.trans_le hcutR
  have hstop : 0<stop := hR.trans_le hRs

  have hcard : Fintype.card I=k := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr order).symm
  let F : SimpleGraph (I⊕J) := recorded selectedRoot (dimerAnchor G) cutoff ⊓
    threshold (dimerAnchor G) cutoff R
  have hforest : F.IsAcyclic :=
    SimpleGraph.IsAcyclic.anti inf_le_left (greedy_isAcyclic selectedRoot _)
  have hroots : RootsSeparated F selectedRoot := by
    intro u v hu hv hreach
    exact greedy_rootsSeparated selectedRoot _ u v hu hv (hreach.mono inf_le_left)
  have hgraph := ordered_graph_bound order F hforest hroots
    (fun i => position G.mesh (G.endpoint (i,0))) G.root cutoff g R (C*R^g)
    (mul_nonneg hC (Real.rpow_nonneg hR.le g))
  have hvalue := forestValue_normalized_bound G (K := K) hcut hcutR hRs hC p hpstop hp hlower
  rw [hcard] at hvalue
  have he : canonicalForestValue G cutoff R C K g (normalized p R)≤
      prefactor G cutoff stop C K g^k*p cutoff^k*R^(-g*(k:ℝ))*
        graphWeight F (dimerAnchor G) cutoff g R (C*R^g) := by
    have hweight : graphWeight F (dimerAnchor G) cutoff g R (C*R^g)=
        (C*R^g)^(recorded selectedRoot (dimerAnchor G) cutoff ⊓
          threshold (dimerAnchor G) cutoff R).edgeFinset.card*
          ∏ e∈(recorded selectedRoot (dimerAnchor G) cutoff ⊓
            threshold (dimerAnchor G) cutoff R).edgeFinset,
            ForestArmRadial.radialEdge (dimerAnchor G) cutoff g R e := by
      unfold graphWeight
      apply congrArg₂ (fun x y : ℝ => x*y)
      · apply congrArg (fun m : ℕ => (C*R^g)^m)
        apply congrArg Finset.card
        ext a
        simp only [SimpleGraph.mem_edgeFinset]
        rfl
      · apply Finset.prod_congr (by ext a; simp only [SimpleGraph.mem_edgeFinset]; rfl)
        intro a _
        rfl
    rw [hweight]
    simpa only [prefactor,mul_assoc] using hvalue
  apply he.trans
  exact mul_le_mul_of_nonneg_left hgraph
    (mul_nonneg (mul_nonneg (pow_nonneg (by unfold prefactor; positivity) _)
      (pow_nonneg (hp cutoff hcut (hcutR.trans hRs)).le _)) (Real.rpow_nonneg hR.le _))

#print axioms actual_forest_ordered_bound
end ExceptionalTimes.CanonicalForestOrdered





