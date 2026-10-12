import ExceptionalTimes.ForestUniformIntegrability
import ExceptionalTimes.OrderedForestIntegral
import ExceptionalTimes.LatticeBadMass

/-! Hölder control of the actual common forest family on excluded anchor
tuples. The moment constant contains only the finite forest family and
fixed macroscopic parameters; it is independent of the mesh and cutoff. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.OrderedForestUI

open ForestUniformIntegrability ForestRelabel RootedAnchorLabels ForestLatticeFamily
open OrderedForestIntegral ForestArmRadial ForestAnchorIntegration ForestCounting LatticeRadial

variable {J : Type*} [Fintype J]

noncomputable def edgeMoment (k : ℕ) (c gp R r : ℝ)
    (G : eligibleForests (fixed k J)) : ℝ :=
  ((radialConstant gp+121/c^2)*R^(2-gp))^(forwardEdges G.val).card*
    (121*r^2)^(k-(forwardEdges G.val).card)

noncomputable def momentConstant (k : ℕ) (c g R r p w : ℝ) : ℝ :=
  ∑ G : eligibleForests (fixed k J),w^(forwardEdges G.val).card*
    (edgeMoment k c (g*p) R r G)^(1/p)

theorem momentConstant_nonneg (k : ℕ) {c g R r p w : ℝ}
    (hgp : g*p<2) (hR : 0≤R) (hw : 0≤w) :
    0≤momentConstant (J := J) k c g R r p w := by
  apply Finset.sum_nonneg
  intro G _
  apply mul_nonneg (pow_nonneg hw _)
  apply Real.rpow_nonneg
  apply mul_nonneg
  · exact pow_nonneg (mul_nonneg (add_nonneg (LatticeForest.radialConstant_nonneg hgp) (by positivity))
      (Real.rpow_nonneg hR _)) _
  · positivity

theorem ordered_forest_bad_bound (k : ℕ) (G : eligibleForests (fixed k J))
    (s : Finset Site) (bad : Finset (Fin k → s))
    {ε b c g R r p q : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g)
    (hpq : Real.HolderConjugate p q) (hgp : g*p<2)
    (hR : 0<R) (hr : ε≤r)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) (root : J → ℂ) :
    ε^(2*k)*(∑ x∈bad,∏ e∈G.val.edgeFinset,
      radialEdge (anchorPosition k (fun v : s => scaledEmbedding ε v) root x) b g R e)≤
      (ε^(2*k)*(bad.card:ℝ))^(1/q)*(edgeMoment k c (g*p) R r G)^(1/p) := by
  let e := Equiv.arrowCongr (free k J).symm (Equiv.refl s)
  have h := forest_bad_mass_bound k (Fintype.card J) (fixed k J) (roots_card k)
    G s (bad.map e.toEmbedding) center hε hc hb hg hpq hgp hR hr hs
    (fun v => root (roots k J v))
  rw [Finset.card_map,Finset.sum_map] at h
  exact h

theorem counted_bad_bound (k : ℕ) (s : Finset Site) (bad : Finset (Fin k → s))
    {ε b c g R r p q w : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g)
    (hpq : Real.HolderConjugate p q) (hgp : g*p<2)
    (hR : 0<R) (hr : ε≤r) (hw : 0≤w)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) (root : J → ℂ) :
    ε^(2*k)*(∑ x∈bad,∑ G : eligibleForests (fixed k J),
      graphWeight G.val (anchorPosition k (fun v : s => scaledEmbedding ε v) root x) b g R w)≤
      (ε^(2*k)*(bad.card:ℝ))^(1/q)*momentConstant (J := J) k c g R r p w := by
  calc
    _ = ∑ G : eligibleForests (fixed k J),w^(forwardEdges G.val).card*
        (ε^(2*k)*(∑ x∈bad,∏ e∈G.val.edgeFinset,
          radialEdge (anchorPosition k (fun v : s => scaledEmbedding ε v) root x) b g R e)) := by
      simp_rw [graphWeight_eq_forward]
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G _
      rw [←Finset.mul_sum]
      ring
    _ ≤ ∑ G : eligibleForests (fixed k J),w^(forwardEdges G.val).card*
        ((ε^(2*k)*(bad.card:ℝ))^(1/q)*(edgeMoment k c (g*p) R r G)^(1/p)) := by
      apply Finset.sum_le_sum
      intro G _
      exact mul_le_mul_of_nonneg_left
        (ordered_forest_bad_bound k G s bad center hε hc hb hg hpq hgp hR hr hs root)
        (pow_nonneg hw _)
    _ = _ := by
      unfold momentConstant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G _
      ring

#print axioms counted_bad_bound
end ExceptionalTimes.OrderedForestUI

