import ExceptionalTimes.ForestLifeGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp

/-! Finite interval charging with the exact inverse-square integral. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestCharge

open MeasureTheory intervalIntegral ForestLifeGeometry KruskalLives ForestGeometry

variable {I : Type*}

/-- Disjoint ordered intervals use at most the full decrease of `1/t` above
their common lower bound. No enumeration of the intervals is assumed. -/
theorem inverse_charge_le (s : Finset I) (u v : I → ℝ) {a : ℝ} (ha : 0 < a)
    (hu : ∀ i ∈ s, a ≤ u i) (huv : ∀ i ∈ s, u i < v i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i ≤ u j ∨ v j ≤ u i) :
    (∑ i ∈ s, (1 / u i - 1 / v i)) ≤ 1 / a := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s u hs
      have hui : 0 < u i := ha.trans_le (hu i hi)
      have hvi : 0 < v i := hui.trans (huv i hi)
      have hafter : ∀ j ∈ s.erase i, v i ≤ u j := by
        intro j hj
        obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
        rcases hdis i hi j hjs hji.symm with h | h
        · exact h
        · exact False.elim ((not_lt_of_ge (hmin j hjs)) ((huv j hjs).trans_le h))
      have hh := ih (s.erase i) (Finset.erase_ssubset hi) hvi hafter
        (fun j hj => huv j (Finset.mem_of_mem_erase hj))
        (fun j hj k hk hne => hdis j (Finset.mem_of_mem_erase hj) k
          (Finset.mem_of_mem_erase hk) hne)
      calc
        _ = (1/u i-1/v i) + ∑ j ∈ s.erase i, (1/u j-1/v j) :=
          (Finset.add_sum_erase s _ hi).symm
        _ ≤ (1/u i-1/v i) + 1/v i := add_le_add le_rfl hh
        _ = 1/u i := by ring
        _ ≤ 1/a := one_div_le_one_div_of_le ha (hu i hi)
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
      positivity

theorem edge_charge_le_one (s : Finset I) (u v : I → ℝ) {ell : ℝ} (hell : 0 < ell)
    (hu : ∀ i ∈ s, ell ≤ u i) (huv : ∀ i ∈ s, u i < v i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i ≤ u j ∨ v j ≤ u i) :
    (∑ i ∈ s, (ell / u i - ell / v i)) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (inverse_charge_le s u v hell hu huv hdis) hell.le
  rw [Finset.mul_sum] at h
  have he : (∑ i ∈ s, ell*(1/u i-1/v i)) = ∑ i ∈ s, (ell/u i-ell/v i) := by
    apply Finset.sum_congr rfl; intro i hi; ring
  rw [he] at h
  simpa [ne_of_gt hell] using h

theorem integral_edge_charge {u v ell : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t in u..v, ell / t^2) = ell/u - ell/v := by
  have hp (t : ℝ) : t ^ (-2 : ℝ) = 1/t^2 := by
    simp [zpow_neg, one_div]
  have h := integral_rpow (a := u) (b := v) (r := -2)
    (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt hu hv⟩)
  simp only [show (-2:ℝ)+1 = -1 by norm_num, Real.rpow_neg_one] at h
  have he : (fun t : ℝ => ell/t^2) = fun t => ell * t^(-2:ℝ) := by
    funext t
    rw [hp]
    ring
  rw [he, intervalIntegral.integral_const_mul, h]
  ring

/-- The actual inverse-square integrals for a recorded edge sum to at most one. -/
theorem integral_edge_charge_le_one (s : Finset I) (u v : I → ℝ) {ell : ℝ} (hell : 0 < ell)
    (hu : ∀ i ∈ s, ell ≤ u i) (huv : ∀ i ∈ s, u i < v i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i ≤ u j ∨ v j ≤ u i) :
    (∑ i ∈ s, ∫ t in u i..v i, ell/t^2) ≤ 1 := by
  have he : (∑ i ∈ s, ∫ t in u i..v i, ell/t^2) = ∑ i ∈ s, (ell/u i-ell/v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_edge_charge (hell.trans_le (hu i hi)) ((hell.trans_le (hu i hi)).trans (huv i hi))
  rw [he]
  exact edge_charge_le_one s u v hell hu huv hdis

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

theorem internal_edge_length_le_birth {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ}
    {S : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    {e : Sym2 V} (he : e ∈ internalEdges (recorded fixed position cutoff) S) :
    clippedEdgeLength position cutoff e ≤ birth fixed position cutoff stop S := by
  by_contra hb
  have hb' := lt_of_not_ge hb
  let t := (birth fixed position cutoff stop S +
    min (clippedEdgeLength position cutoff e) (death fixed position cutoff stop S))/2
  have hmin := lt_min hb' hlife
  have ht : birth fixed position cutoff stop S < t ∧ t < death fixed position cutoff stop S := by
    dsimp [t]
    constructor <;> linarith [min_le_right (clippedEdgeLength position cutoff e)
      (death fixed position cutoff stop S)]
  have hell : t < clippedEdgeLength position cutoff e := by
    dsimp [t]
    linarith [min_le_left (clippedEdgeLength position cutoff e)
      (death fixed position cutoff stop S)]
  exact (not_lt_of_ge (active_internal_edge_length_lt hS hrootless ht he).le) hell

theorem shared_edge_life_intervals {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ}
    {S T : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty) (hne : S ≠ T)
    {e : Sym2 V} (heS : e ∈ internalEdges (recorded fixed position cutoff) S)
    (heT : e ∈ internalEdges (recorded fixed position cutoff) T) :
    death fixed position cutoff stop S ≤ birth fixed position cutoff stop T ∨
      death fixed position cutoff stop T ≤ birth fixed position cutoff stop S := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨a, by simp⟩
  have hxS : x ∈ S := (Finset.mem_filter.mp heS).2 x hx
  have hxT : x ∈ T := (Finset.mem_filter.mp heT).2 x hx
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  obtain ⟨a, ha⟩ := hs.2.2
  obtain ⟨b, hb⟩ := ht.2.2
  rcases le_total s t with hst | hts
  · have hsub : S ⊆ T := by
      rw [ha, hb]
      exact RootKruskal.clusters_nested_of_overlap fixed position cutoff hst (ha ▸ hxS) (hb ▸ hxT)
    exact Or.inl (descendant_death_le_ancestor_birth ⟨s,hs⟩ ⟨t,ht⟩
      ⟨hsub, fun hback => hne (Set.Subset.antisymm hsub hback)⟩)
  · have hsub : T ⊆ S := by
      rw [ha, hb]
      exact RootKruskal.clusters_nested_of_overlap fixed position cutoff hts (hb ▸ hxT) (ha ▸ hxS)
    exact Or.inr (descendant_death_le_ancestor_birth ⟨t,ht⟩ ⟨s,hs⟩
      ⟨hsub, fun hback => hne (Set.Subset.antisymm hback hsub)⟩)

/-- The complete per-edge charge for actual constructed lives. The disjointness
and lower-endpoint conditions are conclusions of the Kruskal geometry. -/
theorem recorded_edge_life_charge_le_one (fixed : V → Prop) (position : V → X)
    {cutoff stop : ℝ} (hb : 0 < cutoff) (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (e : Sym2 V) :
    (∑ S ∈ lives.filter (fun S => e ∈ internalEdges (recorded fixed position cutoff) S),
      ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
        clippedEdgeLength position cutoff e / t^2) ≤ 1 := by
  have hell : 0 < clippedEdgeLength position cutoff e := by
    induction e using Sym2.inductionOn with
    | _ x y => exact hb.trans_le (le_max_right _ _)
  apply integral_edge_charge_le_one _ _ _ hell
  · intro S hS
    obtain ⟨hS, he⟩ := Finset.mem_filter.mp hS
    exact internal_edge_length_le_birth (htimes S hS) (hrootless S hS) (hlife S hS) he
  · intro S hS
    exact hlife S (Finset.mem_filter.mp hS).1
  · intro S hS T hT hne
    obtain ⟨hS, heS⟩ := Finset.mem_filter.mp hS
    obtain ⟨hT, heT⟩ := Finset.mem_filter.mp hT
    exact shared_edge_life_intervals (htimes S hS) (htimes T hT) hne heS heT

theorem total_recorded_charge_le_card (fixed : V → Prop) (position : V → X)
    {cutoff stop : ℝ} (hb : 0 < cutoff) (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, ∑ e ∈ internalEdges (recorded fixed position cutoff) S,
      ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
        clippedEdgeLength position cutoff e / t^2) ≤
      ((recorded fixed position cutoff).edgeFinset.card : ℝ) := by
  have heq : (∑ S ∈ lives, ∑ e ∈ internalEdges (recorded fixed position cutoff) S,
      ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
        clippedEdgeLength position cutoff e / t^2) =
      ∑ e ∈ (recorded fixed position cutoff).edgeFinset,
        ∑ S ∈ lives.filter (fun S => e ∈ internalEdges (recorded fixed position cutoff) S),
          ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
            clippedEdgeLength position cutoff e / t^2 := by
    simp only [internalEdges, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro S hS
    simp only [Finset.mem_filter, he, true_and]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ (recorded fixed position cutoff).edgeFinset, (1 : ℝ) :=
      Finset.sum_le_sum (fun e he => recorded_edge_life_charge_le_one fixed position hb lives
        htimes hrootless hlife e)
    _ = _ := by simp

theorem card_edgeFinset_eq_forwardEdges {N : ℕ} (G : SimpleGraph (Fin N)) :
    G.edgeFinset.card = (ForestCounting.forwardEdges G).card := by
  have h : 2 * G.edgeFinset.card = ∑ u : Fin N, ∑ v : Fin N,
      if G.Adj u v then 1 else 0 := by
    rw [G.two_mul_card_edgeFinset]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  have h' := ForestBridge.twice_forwardEdges G
  simp only [ForestBridge.adjacencyCount] at h'
  omega

/-- The complete internal-edge charge is at most the number of anchors. -/
theorem total_recorded_charge_le (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop : ℝ} (hb : 0 < cutoff) (lives : Finset (Set (Fin (k+J))))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, ∑ e ∈ internalEdges (recorded fixed position cutoff) S,
      ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
        clippedEdgeLength position cutoff e / t^2) ≤ (k : ℝ) := by
  apply (total_recorded_charge_le_card fixed position hb lives htimes hrootless hlife).trans
  rw [card_edgeFinset_eq_forwardEdges]
  exact_mod_cast RootKruskal.greedy_edgeCount_le k J fixed hroots (SortedKruskal.sortedEdges position cutoff)

omit [Fintype V] in
/-- The microscopic enlargement contributes at most its size divided by the
cutoff per life. Its remaining combinatorial cost is the number of lives. -/
theorem enlargement_charge_le (fixed : V → Prop) (position : V → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin) (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
      margin/t^2) ≤ (lives.card : ℝ) * margin/cutoff := by
  calc
    _ ≤ ∑ _S ∈ lives, margin/cutoff := by
      apply Finset.sum_le_sum
      intro S hS
      have hu : cutoff ≤ birth fixed position cutoff stop S := cutoff_le_birth (htimes S hS)
      have hu0 := hb.trans_le hu
      have hv0 := hu0.trans (hlife S hS)
      rw [integral_edge_charge hu0 hv0]
      exact (sub_le_self _ (div_nonneg hm hv0.le)).trans
        (div_le_div_of_nonneg_left hm hb hu)
    _ = _ := by simp; ring

#print axioms inverse_charge_le
#print axioms integral_edge_charge_le_one
#print axioms recorded_edge_life_charge_le_one
#print axioms total_recorded_charge_le
#print axioms enlargement_charge_le

end ExceptionalTimes.ForestCharge

