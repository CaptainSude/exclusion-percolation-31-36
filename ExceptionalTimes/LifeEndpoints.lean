import ExceptionalTimes.ForestLifeCount

/-! Intrinsic endpoint characterizations of actual positive geometric lives.
These identify geometric births from the common recorded forest. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.LifeEndpoints

open SimpleGraph RootKruskal SortedKruskal KruskalLives ForestLifeGeometry ForestGeometry
  ForestCharge ForestLifeCount

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

theorem birth_le_of_internal_le {fixed : V → Prop} {position : V → X}
    {cutoff stop M : ℝ} {S : Set V}
    (htimes : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (hcut : cutoff ≤ M)
    (hbound : ∀ e ∈ internalEdges (recorded fixed position cutoff) S,
      clippedEdgeLength position cutoff e ≤ M) : birth fixed position cutoff stop S ≤ M := by
  by_contra h
  have hM := lt_of_not_ge h
  let t := (M + birth fixed position cutoff stop S)/2
  let s := (birth fixed position cutoff stop S + death fixed position cutoff stop S)/2
  have ht : M < t ∧ t < birth fixed position cutoff stop S := by
    dsimp [t]; constructor <;> linarith
  have hs : birth fixed position cutoff stop S < s ∧ s < death fixed position cutoff stop S := by
    dsimp [s]; constructor <;> linarith
  have hoccs := (interior_mem_lifeTimes htimes hs.1 hs.2).2.2
  obtain ⟨a, ha⟩ := occurs_nonempty hoccs
  have hseq : S = cluster fixed position cutoff s a :=
    occurs_eq_of_overlap hoccs ⟨a, rfl⟩ ha (cluster_self fixed position cutoff s a)
  have hsub : cluster fixed position cutoff t a ⊆ S := by
    rw [hseq]
    exact clusters_nested_of_overlap fixed position cutoff (ht.2.trans hs.1).le
      (cluster_self fixed position cutoff t a) (cluster_self fixed position cutoff s a)
  have hback : S ⊆ cluster fixed position cutoff t a := by
    intro y hy
    have hp := life_reachable_of_internal_short hoccs hrootless
      (fun e he => (hbound e he).trans_lt ht.1) ha hy
    have hh := hp.mono (show recorded fixed position cutoff ⊓ threshold position cutoff t ≤
      contracted (recorded fixed position cutoff ⊓ threshold position cutoff t) fixed from le_sup_left)
    change (contracted (greedy fixed (sortedEdges position cutoff) ⊓ threshold position cutoff t) fixed).Reachable a y at hh
    rw [sorted_threshold_reachable] at hh
    exact hh
  have hocct : Occurs fixed position cutoff S t := ⟨a, Set.Subset.antisymm hback hsub⟩
  have htmem : t ∈ lifeTimes fixed position cutoff stop S :=
    ⟨hcut.trans ht.1.le, (ht.2.trans hlife).le.trans (death_le_stop htimes), hocct⟩
  have hbt : birth fixed position cutoff stop S ≤ t :=
    csInf_le ⟨cutoff, fun _ hr => hr.1⟩ htmem
  exact (not_lt_of_ge hbt) ht.2

/-- The birth is precisely the maximum of the cutoff and all internal
recorded edge lengths. This formulation handles an empty internal edge set. -/
theorem birth_le_iff {fixed : V → Prop} {position : V → X}
    {cutoff stop M : ℝ} {S : Set V}
    (htimes : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    birth fixed position cutoff stop S ≤ M ↔ cutoff ≤ M ∧
      ∀ e ∈ internalEdges (recorded fixed position cutoff) S,
        clippedEdgeLength position cutoff e ≤ M := by
  constructor
  · intro h
    exact ⟨(cutoff_le_birth htimes).trans h,
      fun e he => (internal_edge_length_le_birth htimes hrootless hlife he).trans h⟩
  · rintro ⟨hb, he⟩
    exact birth_le_of_internal_le htimes hrootless hlife hb he

theorem birth_eq_cutoff_of_subsingleton {fixed : V → Prop} {position : V → X}
    {cutoff stop : ℝ} {S : Set V}
    (htimes : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (hsmall : S.Subsingleton) : birth fixed position cutoff stop S = cutoff := by
  apply le_antisymm _ (cutoff_le_birth htimes)
  apply birth_le_of_internal_le htimes hrootless hlife le_rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : (recorded fixed position cutoff).Adj u v := mem_edgeFinset.mp (Finset.mem_filter.mp he).1
    have hu : u ∈ S := (Finset.mem_filter.mp he).2 u (by simp)
    have hv : v ∈ S := (Finset.mem_filter.mp he).2 v (by simp)
    exact False.elim (huv.ne (hsmall hu hv))

omit [Fintype V] [PseudoMetricSpace X] in
theorem reachable_stays_of_closed {G : SimpleGraph V} {S : Set V}
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) {a b : V}
    (ha : a ∈ S) (h : G.Reachable a b) : b ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons h p ih => exact ih (hclosed _ ha _ h)

theorem le_death_of_crossing_le {fixed : V → Prop} {position : V → X}
    {cutoff stop M : ℝ} {S : Set V}
    (htimes : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (hstop : M ≤ stop)
    (hbound : ∀ x ∈ S, ∀ y ∉ S, (recorded fixed position cutoff).Adj x y →
      M ≤ clippedEdgeLength position cutoff s(x,y)) : M ≤ death fixed position cutoff stop S := by
  by_contra h
  have hM := lt_of_not_ge h
  let t := (death fixed position cutoff stop S + M)/2
  have ht : death fixed position cutoff stop S < t ∧ t < M := by
    dsimp [t]; constructor <;> linarith
  obtain ⟨s, hs⟩ := htimes
  have htimes' : (lifeTimes fixed position cutoff stop S).Nonempty := ⟨s, hs⟩
  obtain ⟨a, ha⟩ := occurs_nonempty hs.2.2
  have hclosed : ∀ x ∈ S, ∀ y,
      (contracted (recorded fixed position cutoff ⊓ threshold position cutoff t) fixed).Adj x y → y ∈ S := by
    intro x hx y hxy
    rcases hxy with hxy | hxy
    · by_contra hy
      have hl := hbound x hx y hy hxy.1
      have hlt : clippedEdgeLength position cutoff s(x,y) < t := hxy.2.2
      linarith
    · exact False.elim (hrootless x hx hxy.2.1)
  have hsub : cluster fixed position cutoff t a ⊆ S := by
    intro y hy
    change (contracted (threshold position cutoff t) fixed).Reachable a y at hy
    rw [← sorted_threshold_reachable fixed position cutoff t] at hy
    exact reachable_stays_of_closed hclosed ha hy
  have hback : S ⊆ cluster fixed position cutoff t a := by
    intro y hy
    have hp := life_reachable_of_internal_short hs.2.2 hrootless
      (fun e he => (internal_edge_length_le_birth htimes' hrootless hlife he).trans_lt
        (hlife.trans ht.1)) ha hy
    have hh := hp.mono (show recorded fixed position cutoff ⊓ threshold position cutoff t ≤
      contracted (recorded fixed position cutoff ⊓ threshold position cutoff t) fixed from le_sup_left)
    change (contracted (greedy fixed (sortedEdges position cutoff) ⊓ threshold position cutoff t) fixed).Reachable a y at hh
    rw [sorted_threshold_reachable] at hh
    exact hh
  have htmem : t ∈ lifeTimes fixed position cutoff stop S :=
    ⟨((cutoff_le_birth htimes').trans hlife.le).trans ht.1.le, ht.2.le.trans hstop,
      ⟨a, Set.Subset.antisymm hback hsub⟩⟩
  have htd : t ≤ death fixed position cutoff stop S :=
    le_csSup ⟨stop, fun _ hr => hr.2.1⟩ htmem
  exact (not_lt_of_ge htd) ht.1

/-- Death is precisely the minimum of the stopping scale and the lengths of
recorded edges leaving the life. Thus no rejected candidate enters accounting. -/
theorem le_death_iff {fixed : V → Prop} {position : V → X}
    {cutoff stop M : ℝ} {S : Set V}
    (htimes : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S) :
    M ≤ death fixed position cutoff stop S ↔ M ≤ stop ∧
      ∀ x ∈ S, ∀ y ∉ S, (recorded fixed position cutoff).Adj x y →
        M ≤ clippedEdgeLength position cutoff s(x,y) := by
  constructor
  · intro h
    refine ⟨h.trans (death_le_stop htimes), ?_⟩
    intro x hx y hy _hxy
    exact h.trans ((life_external_distance htimes hlife hx hy).trans (le_max_left _ _))
  · rintro ⟨hs, he⟩
    exact le_death_of_crossing_le htimes hrootless hlife hs he

#print axioms birth_le_iff
#print axioms birth_eq_cutoff_of_subsingleton
#print axioms le_death_iff

end ExceptionalTimes.LifeEndpoints
