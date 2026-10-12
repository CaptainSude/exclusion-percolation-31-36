import ExceptionalTimes.ForestArmWeights

/-! The original fair-site centered response is bounded using the actual
forest buffers. Only local arm necessity and local static probability estimates
remain as inputs; disjointness, independence, charging, and telescoping do not. -/

open scoped BigOperators Classical
open Set
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestArmProbability

open ForestArmWeights ForestProbes ForestTelescope KruskalLives ForestLifeGeometry
open ForestGeometry RootKruskal ProbeProduct EnvironmentVariance CenteredBlocks

variable {V X D : Type*} [Fintype V] [PseudoMetricSpace X]

abbrev Life (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ) :=
  {S // S ∈ positiveLives fixed position cutoff stop}

theorem life_nonempty (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (a : Life fixed position cutoff stop) : a.val.Nonempty := by
  obtain ⟨t, ht⟩ := (positiveLives_spec fixed position cutoff stop a.property).1
  exact occurs_nonempty ht.2.2

noncomputable def center (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (a : Life fixed position cutoff stop) : V :=
  (life_nonempty fixed position cutoff stop a).choose

theorem center_mem (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (a : Life fixed position cutoff stop) : center fixed position cutoff stop a ∈ a.val :=
  (life_nonempty fixed position cutoff stop a).choose_spec

noncomputable def sites (fixed : V → Prop) (position : V → X) (cutoff stop margin : ℝ)
    (sitePosition : D → X) (a : Life fixed position cutoff stop) : Set D :=
  sitePosition ⁻¹' buffer fixed position cutoff stop margin a.val (center fixed position cutoff stop a)

abbrev Grouped (fixed : V → Prop) (position : V → X) (cutoff stop margin : ℝ)
    (sitePosition : D → X) :=
  ({d : D // ∀ a, d ∉ sites fixed position cutoff stop margin sitePosition a} → Bool) ×
    (∀ a, {d : D // d ∈ sites fixed position cutoff stop margin sitePosition a} → Bool)

theorem sites_pairwise (fixed : V → Prop) (position : V → X) {cutoff stop margin : ℝ}
    (sitePosition : D → X) (hb : 0 < cutoff) (hm : margin ≤ cutoff/100) :
    Pairwise (fun a b => Disjoint (sites fixed position cutoff stop margin sitePosition a)
      (sites fixed position cutoff stop margin sitePosition b)) := by
  apply actual_sites_pairwise sitePosition fixed position hb hm Subtype.val Subtype.val_injective
  · intro a
    exact (positiveLives_spec fixed position cutoff stop a.property).1
  · intro a
    exact (positiveLives_spec fixed position cutoff stop a.property).2.1
  · intro a
    exact (positiveLives_spec fixed position cutoff stop a.property).2.2
  · exact center_mem fixed position cutoff stop

/-- Every selected dimer support is outside every actual probe buffer. -/
theorem selected_support_excluded (fixed : V → Prop) (position : V → X)
    {cutoff stop margin : ℝ} (sitePosition : D → X) (hb : 0 < cutoff)
    (hm : margin ≤ cutoff/100) (a : Life fixed position cutoff stop) (v : V) (d : D)
    (hd : dist (position v) (sitePosition d) ≤ margin) :
    d ∉ sites fixed position cutoff stop margin sitePosition a := by
  have h := positiveLives_spec fixed position cutoff stop a.property
  exact support_not_mem_buffer hb hm h.1 h.2.1 h.2.2
    (center_mem fixed position cutoff stop a) v hd

/-- The entire microscopic support of every anchor belonging to this life
lies in the probe's inner pocket. -/
theorem selected_support_in_pocket (fixed : V → Prop) (position : V → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin)
    (a : Life fixed position cutoff stop) {v : V} (hv : v ∈ a.val) {z : X}
    (hz : dist (position v) z ≤ margin) :
    dist (position (center fixed position cutoff stop a)) z <
      (8 * max (birth fixed position cutoff stop a.val)
        (span fixed position cutoff a.val + 2*margin))/2 := by
  have h := positiveLives_spec fixed position cutoff stop a.property
  have hdiam := dist_le_span h.1 h.2.1 (center_mem fixed position cutoff stop a) hv
  have ht := dist_triangle (position (center fixed position cutoff stop a)) (position v) z
  have hu := hb.trans_le (cutoff_le_birth h.1)
  have hleft := le_max_left (birth fixed position cutoff stop a.val)
    (span fixed position cutoff a.val + 2*margin)
  have hright := le_max_right (birth fixed position cutoff stop a.val)
    (span fixed position cutoff a.val + 2*margin)
  linarith

/-- The geometric arm event's full doubled annular corridor lies inside the
independent buffer, for the exact radii used in `lifeCost`. -/
theorem annular_region_subset_buffer (fixed : V → Prop) (position : V → X)
    {cutoff stop margin : ℝ} (hm : 0 ≤ margin) (a : Life fixed position cutoff stop)
    {z : X}
    (hz : (8 * max (birth fixed position cutoff stop a.val)
        (span fixed position cutoff a.val + 2*margin))/2 ≤
          dist (position (center fixed position cutoff stop a)) z ∧
      dist (position (center fixed position cutoff stop a)) z ≤
        2 * (death fixed position cutoff stop a.val / 8)) :
    z ∈ buffer fixed position cutoff stop margin a.val (center fixed position cutoff stop a) := by
  constructor <;> linarith [hz.1, hz.2]

variable [Fintype D] [DecidableEq D]
variable (k J : ℕ)
noncomputable local instance : DecidableEq (Fin (k+J)) := Classical.decEq _

/-- Local events can be a finite union of bulk or boundary arm alternatives.
Their necessity is deliberately an event implication, with no assumed global
probability or forest estimate. -/
theorem centered_forest_bound {I T Q₀ : Type*} [Fintype I] [Fintype T] [DecidableEq T]
    (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop margin C Q g : ℝ} (hb : 0 < cutoff) (hcut : cutoff ≤ stop)
    (hm : 0 ≤ margin) (hsmall : margin ≤ cutoff/100)
    (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hg : 0 ≤ g)
    (α : ℝ → ℝ → ℝ) (hα : ∀ a b, 0 ≤ α a b) (p : ℝ → ℝ)
    (hpnz : ∀ t, p t ≠ 0) (hstop : p stop = 1)
    (hp : ∀ t, 0 < t → t ≤ stop → 0 < p t)
    (hquasi : ∀ a b, 0 < a → a < b → b ≤ stop → α a b ≤ Q * (p a / p b))
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a)
    (sitePosition : D → X) (w : I → (T → PairColor) → ℝ)
    (cross : Grouped fixed position cutoff stop margin sitePosition → Q₀ → T → (I → PairColor) → Bool)
    (outer : Grouped fixed position cutoff stop margin sitePosition → (Q₀ × T → Bool) → ℝ)
    (E : ∀ a, ({d : D // d ∈ sites fixed position cutoff stop margin sitePosition a} → Bool) → Prop)
    (hw : ∀ i, ∑ h, w i h = 0)
    (hf : ∀ o h, |outer o (historyTests (cross o) h)| ≤ 1)
    (hnecessary : ∀ o, AllEndpointPivotal (cross o) → ∀ a, E a (o.2 a))
    (hstatic : ∀ a, probability (fairSites {d : D // d ∈ sites fixed position cutoff stop margin sitePosition a})
      (E a) ≤ lifeCost fixed position cutoff stop margin α a.val) :
    |(fairSites D).expect (fun ω =>
      let o := groupColors (sites fixed position cutoff stop margin sitePosition) ω
      kernel w (fun h => outer o (historyTests (cross o) h)))| ≤
      (∏ i, variation (w i)) *
        (((Q*C^2*256^g)^2 * Real.exp (g*(1+4*margin/cutoff)))^k *
          (p cutoff^k /
            ∏ e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset,
              p (clippedEdgeLength position cutoff e))) := by
  let P := sites fixed position cutoff stop margin sitePosition
  let ν₀ := fairSites {d : D // ∀ a, d ∉ P a}
  let ν := fun a => fairSites {d : D // d ∈ P a}
  let f := fun o => kernel w (fun h => outer o (historyTests (cross o) h))
  change |(fairSites D).expect (fun ω => f (groupColors P ω))| ≤ _
  rw [fairSites_partition P (sites_pairwise fixed position sitePosition hb hsmall) f]
  have hv : 0 ≤ ∏ i, variation (w i) :=
    Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun h _ => abs_nonneg (w i h)))
  have hlocal : (∏ a, probability (ν a) (E a)) ≤
      ∏ a : Life fixed position cutoff stop, lifeCost fixed position cutoff stop margin α a.val :=
    Finset.prod_le_prod₀ (fun a _ => probability_nonneg _ _) (fun a _ => hstatic a)
  have hforest := actual_forest_arm_product k J fixed hroots position hb hcut hm hC hQ hg
    α hα p hpnz hstop hp hquasi hlower
  have hproducts : (∏ a : Life fixed position cutoff stop, lifeCost fixed position cutoff stop margin α a.val) =
      ∏ S ∈ positiveLives fixed position cutoff stop, lifeCost fixed position cutoff stop margin α S :=
    Finset.prod_coe_sort _ _
  calc
    _ ≤ (∏ i, variation (w i)) * ∏ a, probability (ν a) (E a) :=
      centered_probe_bound ν₀ ν w cross outer E hw hf hnecessary
    _ ≤ (∏ i, variation (w i)) * ∏ a : Life fixed position cutoff stop,
        lifeCost fixed position cutoff stop margin α a.val := mul_le_mul_of_nonneg_left hlocal hv
    _ ≤ _ := mul_le_mul_of_nonneg_left (hproducts.trans_le hforest) hv

#print axioms centered_forest_bound

end ExceptionalTimes.ForestArmProbability
