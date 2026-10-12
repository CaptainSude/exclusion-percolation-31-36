import ExceptionalTimes.SortedKruskal

/-! Internal recorded edges of actual ungrounded lives. The metric diameter
bound and the scale condition on every charged edge are derived from the one
globally sorted forest and its threshold-component identity. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestLifeGeometry

open RootKruskal SortedKruskal KruskalLives ForestGeometry SimpleGraph

variable {V X : Type*} [PseudoMetricSpace X]

/-- Virtual root edges cannot be used by a component containing no root. -/
theorem ordinary_reachable_of_rootless (G : SimpleGraph V) (fixed : V → Prop)
    {a b : V} (h : (contracted G fixed).Reachable a b)
    (hrootless : ∀ r, fixed r → ¬ (contracted G fixed).Reachable a r) : G.Reachable a b := by
  obtain ⟨p⟩ := h
  revert hrootless
  induction p with
  | nil => intro _; exact Reachable.rfl
  | @cons a c b hab p ih =>
    intro hrootless
    have hc : ∀ r, fixed r → ¬ (contracted G fixed).Reachable c r := by
      intro r hr hcr
      exact hrootless r hr (hab.reachable.trans hcr)
    rcases hab with hab | hab
    · exact hab.reachable.trans (ih hc)
    · exact False.elim (hrootless a hab.2.1 Reachable.rfl)

variable [Fintype V]

noncomputable def recorded (fixed : V → Prop) (position : V → X) (cutoff : ℝ) : SimpleGraph V :=
  greedy fixed (sortedEdges position cutoff)

noncomputable def internalEdges (G : SimpleGraph V) (S : Set V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)

theorem life_ordinary_reachable {fixed : V → Prop} {position : V → X} {cutoff t : ℝ}
    {S : Set V} (hS : Occurs fixed position cutoff S t)
    (hrootless : ∀ r ∈ S, ¬ fixed r) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (recorded fixed position cutoff ⊓ threshold position cutoff t).Reachable x y := by
  obtain ⟨a, ha⟩ := hS
  have hx' : (contracted (threshold position cutoff t) fixed).Reachable a x := by
    change x ∈ cluster fixed position cutoff t a
    rwa [← ha]
  have hy' : (contracted (threshold position cutoff t) fixed).Reachable a y := by
    change y ∈ cluster fixed position cutoff t a
    rwa [← ha]
  have he := sorted_threshold_reachable fixed position cutoff t
  apply ordinary_reachable_of_rootless _ fixed
  · change (contracted (greedy fixed (sortedEdges position cutoff) ⊓ threshold position cutoff t) fixed).Reachable x y
    rw [he]
    exact hx'.symm.trans hy'
  · intro r hr hxr
    change (contracted (greedy fixed (sortedEdges position cutoff) ⊓ threshold position cutoff t) fixed).Reachable x r at hxr
    rw [he] at hxr
    exact hrootless r (ha.symm ▸ hx'.trans hxr) hr

theorem recorded_reachable_stays_in_life {fixed : V → Prop} {position : V → X} {cutoff t : ℝ}
    {S : Set V} (hS : Occurs fixed position cutoff S t) {x y : V} (hx : x ∈ S)
    (hxy : (recorded fixed position cutoff ⊓ threshold position cutoff t).Reachable x y) : y ∈ S := by
  obtain ⟨a, ha⟩ := hS
  have hh := hxy.mono (show recorded fixed position cutoff ⊓ threshold position cutoff t ≤
      contracted (recorded fixed position cutoff ⊓ threshold position cutoff t) fixed from le_sup_left)
  change (contracted (greedy fixed (sortedEdges position cutoff) ⊓ threshold position cutoff t) fixed).Reachable x y at hh
  rw [sorted_threshold_reachable] at hh
  have hx' : (contracted (threshold position cutoff t) fixed).Reachable a x := by
    change x ∈ cluster fixed position cutoff t a
    rwa [← ha]
  exact ha.symm ▸ hx'.trans hh

/-- The diameter of a life is bounded by its internal edges in the common
recorded forest, with no factor depending on the number of anchors. -/
theorem life_distance_le_internal_sum {fixed : V → Prop} {position : V → X} {cutoff t : ℝ}
    {S : Set V} (hS : Occurs fixed position cutoff S t)
    (hrootless : ∀ r ∈ S, ¬ fixed r) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    dist (position x) (position y) ≤
      ∑ e ∈ internalEdges (recorded fixed position cutoff) S, clippedEdgeLength position cutoff e := by
  obtain ⟨p, hp⟩ := (life_ordinary_reachable hS hrootless hx hy).exists_isPath
  apply dist_le_recorded_edge_sum position cutoff p hp.isTrail
  intro e he
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_edgeFinset.mpr
    exact edgeSet_mono inf_le_left (p.edges_subset_edgeSet he)
  · intro z hz
    have hsupport := p.mem_support_of_mem_edges he hz
    exact recorded_reachable_stays_in_life hS hx ⟨p.takeUntil z hsupport⟩

omit [Fintype V] in
theorem edge_of_reachable_in_acyclic_subgraph {G H : SimpleGraph V} (hG : G.IsAcyclic)
    (hHG : H ≤ G) {x y : V} (hxy : G.Adj x y) (hr : H.Reachable x y) : H.Adj x y := by
  have he : edge x y ≤ G := by
    intro a b hab
    rcases (edge_adj x y a b).mp hab with ⟨h | h, _⟩
    · rcases h with ⟨rfl,rfl⟩; exact hxy
    · rcases h with ⟨rfl,rfl⟩; exact hxy.symm
  have hh : (H ⊔ edge x y).IsAcyclic := hG.anti (sup_le hHG he)
  exact ((isAcyclic_sup_fromEdgeSet_iff.mp hh).2 hr).resolve_left hxy.ne

/-- Every internal recorded edge of a live component has already appeared.
Thus its clipped length is below the current scale. -/
theorem internal_edge_length_lt {fixed : V → Prop} {position : V → X} {cutoff t : ℝ}
    {S : Set V} (hS : Occurs fixed position cutoff S t) (hrootless : ∀ r ∈ S, ¬ fixed r)
    {e : Sym2 V} (he : e ∈ internalEdges (recorded fixed position cutoff) S) :
    clippedEdgeLength position cutoff e < t := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy : (recorded fixed position cutoff).Adj x y :=
      mem_edgeFinset.mp (Finset.mem_filter.mp he).1
    have hx : x ∈ S := (Finset.mem_filter.mp he).2 x (by simp)
    have hy : y ∈ S := (Finset.mem_filter.mp he).2 y (by simp)
    have hh := edge_of_reachable_in_acyclic_subgraph
      (greedy_isAcyclic fixed (sortedEdges position cutoff)) inf_le_left hxy
      (life_ordinary_reachable hS hrootless hx hy)
    exact hh.2.2

/-- The same charged edge condition throughout the constructed open life. -/
theorem active_internal_edge_length_lt {fixed : V → Prop} {position : V → X} {cutoff stop t : ℝ}
    {S : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r)
    (ht : birth fixed position cutoff stop S < t ∧ t < death fixed position cutoff stop S)
    {e : Sym2 V} (he : e ∈ internalEdges (recorded fixed position cutoff) S) :
    clippedEdgeLength position cutoff e < t :=
  internal_edge_length_lt (interior_mem_lifeTimes hS ht.1 ht.2).2.2 hrootless he

#print axioms life_distance_le_internal_sum
#print axioms internal_edge_length_lt
#print axioms active_internal_edge_length_lt

end ExceptionalTimes.ForestLifeGeometry

