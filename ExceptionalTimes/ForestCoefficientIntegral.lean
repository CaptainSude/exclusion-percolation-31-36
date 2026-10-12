import ExceptionalTimes.ForestWeightedAnchors
import ExceptionalTimes.OptimizedForestMajorant

/-! A summable superfactorial bound for the literal lattice forest
integrals, including the exact insertion factorial. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestCoefficientIntegral

open ForestAnchorIntegration ForestWeightedAnchors ForestLatticeFamily ForestArmRadial
open LatticeRadial LatticeForest ForestCounting OptimizedForestMajorant

theorem scale_edge_gain {R A C g : ℝ} (hR : 0<R) :
    (A*R^g)*C*R^(2-g)=(A*C)*R^2 := by
  calc
    _ = (A*C)*(R^g*R^(2-g)) := by ring
    _ = _ := by rw [←Real.rpow_add hR]; norm_num

noncomputable def summationConstant (J : ℕ) (d D A c g r₀ : ℝ) : ℝ :=
  d^(-g)*max (A*(radialConstant g+121/c^2)*D^2) (121*r₀^2)*
    (Real.exp 1*Real.exp (((J:ℝ)+1)^2))

theorem summationConstant_nonneg (J : ℕ) {d D A c g r₀ : ℝ}
    (hd : 0≤d) : 0≤summationConstant J d D A c g r₀ := by
  unfold summationConstant
  apply mul_nonneg _ (by positivity)
  exact mul_nonneg (Real.rpow_nonneg hd _) ((by positivity : (0:ℝ)≤121*r₀^2).trans (le_max_right _ _))

theorem counted_lattice_forest_bound (k J : ℕ) (hk : 1≤k)
    (fixed : Fin (k+J) → Prop) (hrootsize : Fintype.card {v // fixed v}=J)
    (s : Finset Site) {ε b c g R r₀ A d D : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hR : 0<R) (hr₀ : ε≤r₀) (hA : 0≤A) (hd : 0<d)
    (hlower : d*(k:ℝ)^(-(1/2:ℝ))≤R)
    (hupper : R≤D*(k:ℝ)^(-(1/2:ℝ)))
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀)
    (root : {v // fixed v} → ℂ) :
    R^(-g*(k:ℝ))/(k.factorial:ℝ)*
      (ε^(2*k)*(∑ x : {v // ¬fixed v} → s, ∑ G : eligibleForests fixed,
        (A*R^g)^(forwardEdges G.val).card*∏ e∈G.val.edgeFinset,
          radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e))≤
      (summationConstant J d D A c g r₀)^k*(k:ℝ)^(-(1-g/2)*k) := by
  have hintegral := weighted_forests_anchor_sum k J fixed hrootsize s center hε hc hb hg hg2 hR hr₀
    (mul_nonneg hA (Real.rpow_nonneg hR.le g)) hs root
  rw [scale_edge_gain hR] at hintegral
  have hrad : 0≤radialConstant g+121/c^2 :=
    add_nonneg (radialConstant_nonneg hg2) (by positivity)
  have h := counted_majorant k J hk (M := 121*r₀^2) hR hd (mul_nonneg hA hrad) (by positivity) hg hlower hupper
  exact (mul_le_mul_of_nonneg_left hintegral
    (div_nonneg (Real.rpow_nonneg hR.le _) (Nat.cast_nonneg k.factorial))).trans h

theorem summable_lattice_forest_majorant (J : ℕ) {d D A c g r₀ : ℝ}
    (hd : 0≤d) (hg2 : g<2) :
    Summable (fun k : ℕ => (summationConstant J d D A c g r₀)^k*(k:ℝ)^(-(1-g/2)*k)) :=
  summable_superfactor (summationConstant_nonneg J hd) (by linarith)

#print axioms counted_lattice_forest_bound
#print axioms summable_lattice_forest_majorant

end ExceptionalTimes.ForestCoefficientIntegral

