import ExceptionalTimes.ForestCharge
import Mathlib.Data.Finset.Max

/-! The number of actual positive ungrounded lives is at most twice the
number of anchors, by an injection into anchors and internal recorded edges. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestLifeCount

open SimpleGraph RootKruskal SortedKruskal KruskalLives ForestLifeGeometry ForestGeometry

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

theorem life_reachable_of_internal_short {fixed : V → Prop} {position : V → X} {cutoff s t : ℝ}
    {S : Set V} (hS : Occurs fixed position cutoff S s) (hrootless : ∀ r ∈ S, ¬ fixed r)
    (hshort : ∀ e ∈ internalEdges (recorded fixed position cutoff) S,
      clippedEdgeLength position cutoff e < t)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (recorded fixed position cutoff ⊓ threshold position cutoff t).Reachable x y := by
  obtain ⟨p⟩ := life_ordinary_reachable hS hrootless hx hy
  have hsupp : ∀ z ∈ p.support, z ∈ S := fun z hz =>
    recorded_reachable_stays_in_life hS hx ⟨p.takeUntil z hz⟩
  let p' := (p.mapLe inf_le_left).induce S (by
    intro z hz
    exact hsupp z (by simpa only [Walk.support_map, Hom.coe_ofLE, List.map_id_fun, id_eq] using hz))
  let φ : (recorded fixed position cutoff).induce S →g
      (recorded fixed position cutoff ⊓ threshold position cutoff t) := {
    toFun := Subtype.val
    map_rel' := by
      intro a b hab
      change (recorded fixed position cutoff).Adj a.val b.val at hab
      refine ⟨hab, hab.ne, ?_⟩
      apply hshort s(a.val,b.val)
      apply Finset.mem_filter.mpr
      refine ⟨mem_edgeFinset.mpr hab, ?_⟩
      intro z hz
      have hz' : z = a.val ∨ z = b.val := by simpa using hz
      rcases hz' with rfl | rfl
      · exact a.property
      · exact b.property }
  exact ⟨p'.map φ⟩

theorem internalEdges_nonempty_of_not_subsingleton {fixed : V → Prop} {position : V → X}
    {cutoff t : ℝ} {S : Set V} (hS : Occurs fixed position cutoff S t)
    (hrootless : ∀ r ∈ S, ¬ fixed r) (hlarge : ¬ S.Subsingleton) :
    (internalEdges (recorded fixed position cutoff) S).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp hlarge
  obtain ⟨p⟩ := life_ordinary_reachable hS hrootless hx hy
  cases p with
  | nil => exact False.elim (hxy rfl)
  | @cons x z y hxz p =>
    refine ⟨s(x,z), Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr hxz.1, ?_⟩⟩
    intro w hw
    have hw' : w = x ∨ w = z := by simpa using hw
    rcases hw' with rfl | rfl
    · exact hx
    · exact recorded_reachable_stays_in_life hS hx hxz.reachable

/-- Distinct positive lives cannot choose the same maximal internal edge.
The proof works directly with connectivity at their interior scales. -/
theorem eq_of_same_maximal_internal_edge {fixed : V → Prop} {position : V → X}
    {cutoff stop : ℝ} {S T : Set V}
    (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty)
    (hrS : ∀ r ∈ S, ¬ fixed r) (hrT : ∀ r ∈ T, ¬ fixed r)
    (hlS : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (hlT : birth fixed position cutoff stop T < death fixed position cutoff stop T)
    {e : Sym2 V} (heS : e ∈ internalEdges (recorded fixed position cutoff) S)
    (heT : e ∈ internalEdges (recorded fixed position cutoff) T)
    (hmaxS : ∀ f ∈ internalEdges (recorded fixed position cutoff) S,
      clippedEdgeLength position cutoff f ≤ clippedEdgeLength position cutoff e)
    (hmaxT : ∀ f ∈ internalEdges (recorded fixed position cutoff) T,
      clippedEdgeLength position cutoff f ≤ clippedEdgeLength position cutoff e) : S = T := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e := by
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨a, by simp⟩
  have hxS : x ∈ S := (Finset.mem_filter.mp heS).2 x hx
  have hxT : x ∈ T := (Finset.mem_filter.mp heT).2 x hx
  let s := (birth fixed position cutoff stop S + death fixed position cutoff stop S)/2
  let t := (birth fixed position cutoff stop T + death fixed position cutoff stop T)/2
  have hs : birth fixed position cutoff stop S < s ∧ s < death fixed position cutoff stop S := by
    dsimp [s]; constructor <;> linarith
  have ht : birth fixed position cutoff stop T < t ∧ t < death fixed position cutoff stop T := by
    dsimp [t]; constructor <;> linarith
  have hoccS := (interior_mem_lifeTimes hS hs.1 hs.2).2.2
  have hoccT := (interior_mem_lifeTimes hT ht.1 ht.2).2.2
  have hellS := internal_edge_length_lt hoccS hrS heS
  have hellT := internal_edge_length_lt hoccT hrT heT
  apply Set.Subset.antisymm
  · intro y hy
    have hp := life_reachable_of_internal_short hoccS hrS
      (fun f hf => (hmaxS f hf).trans_lt hellT) hxS hy
    exact recorded_reachable_stays_in_life hoccT hxT hp
  · intro y hy
    have hp := life_reachable_of_internal_short hoccT hrT
      (fun f hf => (hmaxT f hf).trans_lt hellS) hxT hy
    exact recorded_reachable_stays_in_life hoccS hxS hp

theorem large_lives_card_le_edges (fixed : V → Prop) (position : V → X)
    {cutoff stop : ℝ} (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (lives.filter (fun S => ¬ S.Subsingleton)).card ≤
      (recorded fixed position cutoff).edgeFinset.card := by
  classical
  let large := lives.filter (fun S => ¬ S.Subsingleton)
  have hex : ∀ S : large, ∃ e : (recorded fixed position cutoff).edgeFinset,
      e.val ∈ internalEdges (recorded fixed position cutoff) S.val ∧
      ∀ f ∈ internalEdges (recorded fixed position cutoff) S.val,
        clippedEdgeLength position cutoff f ≤ clippedEdgeLength position cutoff e.val := by
    intro S
    have hS := Finset.mem_filter.mp S.property
    obtain ⟨t, ht⟩ := htimes S.val hS.1
    have hn := internalEdges_nonempty_of_not_subsingleton ht.2.2
      (hrootless S.val hS.1) hS.2
    obtain ⟨e, he, hmax⟩ := Finset.exists_max_image _ (clippedEdgeLength position cutoff) hn
    exact ⟨⟨e, (Finset.mem_filter.mp he).1⟩, he, hmax⟩
  choose m hm using hex
  have hinj : Function.Injective m := by
    intro S T h
    have hS := (Finset.mem_filter.mp S.property).1
    have hT := (Finset.mem_filter.mp T.property).1
    apply Subtype.ext
    apply eq_of_same_maximal_internal_edge (htimes _ hS) (htimes _ hT)
      (hrootless _ hS) (hrootless _ hT) (hlife _ hS) (hlife _ hT) (hm S).1
    · simpa only [h] using (hm T).1
    · exact (hm S).2
    · simpa only [h] using (hm T).2
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective m hinj

theorem small_lives_card_le_anchors (fixed : V → Prop) (position : V → X)
    {cutoff stop : ℝ} (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r) :
    (lives.filter (fun S => S.Subsingleton)).card ≤ Fintype.card {v // ¬ fixed v} := by
  classical
  let small := lives.filter (fun S => S.Subsingleton)
  have hex : ∀ S : small, ∃ x : {v // ¬ fixed v}, x.val ∈ S.val := by
    intro S
    have hS := (Finset.mem_filter.mp S.property).1
    obtain ⟨t, ht⟩ := htimes S.val hS
    obtain ⟨x, hx⟩ := occurs_nonempty ht.2.2
    exact ⟨⟨x, hrootless S.val hS x hx⟩, hx⟩
  choose m hm using hex
  have hinj : Function.Injective m := by
    intro S T h
    apply Subtype.ext
    have hS := (Finset.mem_filter.mp S.property).2.eq_singleton_of_mem (hm S)
    have hT := (Finset.mem_filter.mp T.property).2.eq_singleton_of_mem (hm T)
    exact hS.trans (by simpa only [h] using hT.symm)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective m hinj

/-- Every positive rootless life is charged injectively either to its sole
anchor or to a maximal internal edge of the common recorded forest. -/
theorem lives_card_le (fixed : V → Prop) (position : V → X)
    {cutoff stop : ℝ} (lives : Finset (Set V))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    lives.card ≤ Fintype.card {v // ¬ fixed v} + (recorded fixed position cutoff).edgeFinset.card := by
  rw [← Finset.card_filter_add_card_filter_not (s := lives) (fun S => S.Subsingleton)]
  exact Nat.add_le_add (small_lives_card_le_anchors fixed position lives htimes hrootless)
    (large_lives_card_le_edges fixed position lives htimes hrootless hlife)

theorem lives_card_le_twice (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop : ℝ} (lives : Finset (Set (Fin (k+J))))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    lives.card ≤ 2*k := by
  have h := lives_card_le fixed position lives htimes hrootless hlife
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hroots,
    ForestCharge.card_edgeFinset_eq_forwardEdges] at h
  have he := RootKruskal.greedy_edgeCount_le k J fixed hroots (SortedKruskal.sortedEdges position cutoff)
  change (ForestCounting.forwardEdges (recorded fixed position cutoff)).card ≤ k at he
  omega

theorem enlargement_charge_le_twice (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin)
    (lives : Finset (Set (Fin (k+J))))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
      margin/t^2) ≤ (2*k : ℝ) * margin/cutoff := by
  apply (ForestCharge.enlargement_charge_le fixed position hb hm lives htimes hlife).trans
  apply div_le_div_of_nonneg_right _ hb.le
  apply mul_le_mul_of_nonneg_right _ hm
  exact_mod_cast lives_card_le_twice k J fixed hroots position lives htimes hrootless hlife

/-- Both diameter-edge and microscopic-enlargement charges of the actual
root-contracted construction have a bound linear in the number of anchors. -/
theorem total_charge_le (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : 0 ≤ margin)
    (lives : Finset (Set (Fin (k+J))))
    (htimes : ∀ S ∈ lives, (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ S ∈ lives, ∀ r ∈ S, ¬ fixed r)
    (hlife : ∀ S ∈ lives, birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    (∑ S ∈ lives, ∑ e ∈ internalEdges (recorded fixed position cutoff) S,
      ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
        clippedEdgeLength position cutoff e / t^2) +
    (∑ S ∈ lives, ∫ t in birth fixed position cutoff stop S..death fixed position cutoff stop S,
      margin/t^2) ≤ (k : ℝ) + (2*k : ℝ) * margin/cutoff :=
  add_le_add (ForestCharge.total_recorded_charge_le k J fixed hroots position hb lives htimes hrootless hlife)
    (enlargement_charge_le_twice k J fixed hroots position hb hm lives htimes hrootless hlife)

#print axioms eq_of_same_maximal_internal_edge
#print axioms lives_card_le_twice
#print axioms total_charge_le

end ExceptionalTimes.ForestLifeCount
