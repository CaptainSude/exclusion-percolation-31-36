import ExceptionalTimes.ForestArmWeights
import ExceptionalTimes.LatticeRadial

/-! The exact arm profile edge factor is bounded by the concrete clipped radial
kernel already integrated in `LatticeRadial`. Only the local lower-power estimate
is used; the forest support is the actual threshold-truncated Kruskal graph. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestArmRadial

open ForestArmWeights ForestTelescope ForestLifeGeometry ForestGeometry RootKruskal

theorem inverse_profile_le (p : ℝ → ℝ) {C g r stop : ℝ} (hr : 0 < r)
    (hrstop : r ≤ stop) (hp : 0 < p r) (hstop : p stop = 1)
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    1 / p r ≤ C * stop^g * r^(-g) := by
  apply (div_le_iff₀ hp).mpr
  have h := hlower r stop hr hrstop le_rfl
  rw [hstop, Real.div_rpow (hr.trans_le hrstop).le hr.le,
    div_eq_mul_inv] at h
  rw [Real.rpow_neg hr.le]
  convert h using 1
  ring

variable {V X : Type*} [PseudoMetricSpace X]

noncomputable def radialEdge (position : V → X) (cutoff g stop : ℝ) (e : Sym2 V) : ℝ :=
  if clippedEdgeLength position cutoff e < stop then
    (clippedEdgeLength position cutoff e)^(-g) else 0

@[simp] theorem radialEdge_mk (position : V → X) (cutoff g stop : ℝ) (u v : V) :
    radialEdge position cutoff g stop s(u,v) =
      LatticeRadial.clippedKernel (dist (position u) (position v)) cutoff g stop := rfl

theorem radialEdge_nonneg (position : V → X) (cutoff g stop : ℝ) (e : Sym2 V) :
    0 ≤ radialEdge position cutoff g stop e := by
  unfold radialEdge
  split_ifs
  · exact Real.rpow_nonneg (clippedEdgeLength_nonneg _ _ _) _
  · exact le_rfl

variable [Fintype V]

theorem short_edge_length (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    {e : Sym2 V} (he : e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset) :
    clippedEdgeLength position cutoff e < stop := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have h : (recorded fixed position cutoff ⊓ threshold position cutoff stop).Adj u v :=
      SimpleGraph.mem_edgeFinset.mp he
    exact h.2.2

theorem profile_edge_product_le (fixed : V → Prop) (position : V → X)
    {cutoff stop C g : ℝ} (hb : 0 < cutoff) (p : ℝ → ℝ) (hstop : p stop = 1)
    (hp : ∀ t, 0 < t → t ≤ stop → 0 < p t)
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    (∏ e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset,
      1/p (clippedEdgeLength position cutoff e)) ≤
      (C*stop^g)^((recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset.card) *
        ∏ e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset,
          radialEdge position cutoff g stop e := by
  let E := (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset
  have hpos (e : Sym2 V) : 0 < clippedEdgeLength position cutoff e := by
    induction e using Sym2.inductionOn with
    | _ u v => exact hb.trans_le (le_max_right _ _)
  calc
    _ ≤ ∏ e ∈ E, (C*stop^g) * radialEdge position cutoff g stop e := by
      apply Finset.prod_le_prod₀
      · intro e he
        exact (one_div_pos.mpr (hp _ (hpos e) (short_edge_length fixed position cutoff stop he).le)).le
      · intro e he
        have hs := short_edge_length fixed position cutoff stop he
        rw [radialEdge, ite_eq_left hs]
        exact inverse_profile_le p (hpos e) hs.le (hp _ (hpos e) hs.le) hstop hlower
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

variable (k J : ℕ)
noncomputable local instance : DecidableEq (Fin (k+J)) := Classical.decEq _

/-- The proved arm product is now a product of literal radial edge kernels.
These are exactly `clippedKernel dist cutoff g stop`, including the cutoff atom. -/
theorem actual_forest_radial_bound (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop margin C Q g : ℝ} (hb : 0 < cutoff) (hcut : cutoff ≤ stop)
    (hm : 0 ≤ margin) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hg : 0 ≤ g)
    (α : ℝ → ℝ → ℝ) (hα : ∀ a b, 0 ≤ α a b) (p : ℝ → ℝ)
    (hpnz : ∀ t, p t ≠ 0) (hstop : p stop = 1)
    (hp : ∀ t, 0 < t → t ≤ stop → 0 < p t)
    (hquasi : ∀ a b, 0 < a → a < b → b ≤ stop → α a b ≤ Q * (p a / p b))
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    (∏ S ∈ positiveLives fixed position cutoff stop, lifeCost fixed position cutoff stop margin α S) ≤
      ((Q*C^2*256^g)^2 * Real.exp (g*(1+4*margin/cutoff)))^k * p cutoff^k *
        (C*stop^g)^((recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset.card) *
          ∏ e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset,
            radialEdge position cutoff g stop e := by
  have h := actual_forest_arm_product k J fixed hroots position hb hcut hm hC hQ hg
    α hα p hpnz hstop hp hquasi hlower
  have hedges := profile_edge_product_le fixed position hb p hstop hp hlower
  have hp0 := (hp cutoff hb hcut).le
  let A := ((Q*C^2*256^g)^2 * Real.exp (g*(1+4*margin/cutoff)))^k
  have hA : 0 ≤ A := by positivity
  apply h.trans
  have hscaled := mul_le_mul_of_nonneg_left hedges (mul_nonneg hA (pow_nonneg hp0 k))
  simp only [one_div, Finset.prod_inv_distrib] at hscaled
  convert hscaled using 1 <;> dsimp [A] <;> ring

#print axioms profile_edge_product_le
#print axioms actual_forest_radial_bound

end ExceptionalTimes.ForestArmRadial
