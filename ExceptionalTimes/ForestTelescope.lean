import ExceptionalTimes.KruskalEpisodes

/-! Exact arm-function telescoping on a finite family of actual positive
rootless lives. Both the family and its endpoint dictionary are constructed. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestTelescope

open SimpleGraph RootKruskal SortedKruskal KruskalComponents KruskalLedger KruskalEpisodes
  KruskalLifeDictionary KruskalLives ForestLifeGeometry ForestGeometry

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

noncomputable def execution (position : V → X) (cutoff stop : ℝ) : List (V × V) :=
  (sortedEdges position cutoff).filter (fun e => length position cutoff e < stop)

noncomputable def records (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ) : List (Episode V) :=
  allEpisodes fixed cutoff stop (length position cutoff) (execution position cutoff stop)

theorem record_nonnegative_duration (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (hcut : cutoff ≤ stop) {E : Episode V} (hE : E ∈ records fixed position cutoff stop) : E.born ≤ E.ends := by
  simp only [records, allEpisodes, List.mem_append] at hE
  rcases hE with hE | hE
  · obtain ⟨pre, e, tail, hfull, _haccept, _hS, _hside, hborn, hends⟩ :=
      closed_episode_origin fixed cutoff (length position cutoff) _ hE
    have hsort : (execution position cutoff stop).Pairwise
        (fun e f => length position cutoff f ≤ length position cutoff e) :=
      List.Pairwise.filter _ (sortedEdges_pairwise position cutoff)
    rw [hfull] at hsort
    have hhead := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1
    rw [hborn, hends]
    exact birthAt_le_bound fixed cutoff (length position cutoff e) (length position cutoff) tail
      (le_max_right _ _) hhead _
  · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hE
    apply birthAt_le_bound fixed cutoff stop (length position cutoff) _ hcut
    intro e he
    exact (of_decide_eq_true (List.mem_filter.mp he).2).le

theorem positive_record_is_life (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    {E : Episode V} (hE : E ∈ records fixed position cutoff stop) (hpos : E.born < E.ends) :
    (lifeTimes fixed position cutoff stop E.anchors).Nonempty ∧
      (∀ r ∈ E.anchors, ¬ fixed r) ∧
      birth fixed position cutoff stop E.anchors = E.born ∧
      death fixed position cutoff stop E.anchors = E.ends := by
  simp only [records, allEpisodes, List.mem_append] at hE
  rcases hE with hE | hE
  · obtain ⟨pre, e, tail, hfull, haccept, hS, hside, hborn, hends⟩ :=
      closed_episode_origin fixed cutoff (length position cutoff) _ hE
    obtain ⟨before, hbefore⟩ := filter_below_suffix (length position cutoff) stop
      (sortedEdges position cutoff) (sortedEdges_pairwise position cutoff)
    have hall : sortedEdges position cutoff = (before ++ pre) ++ e :: tail := by
      rw [hbefore]
      change before ++ execution position cutoff stop = _
      rw [hfull, List.append_assoc]
    have he : e ∈ execution position cutoff stop := by rw [hfull]; simp
    have hstop := (of_decide_eq_true (List.mem_filter.mp he).2).le
    have hp : birthAt fixed cutoff (length position cutoff) tail E.anchors < length position cutoff e := by
      rwa [← hborn, ← hends]
    obtain ⟨ht, hb, hd⟩ := positive_ending_is_life fixed position cutoff stop (before ++ pre) tail e
      hall haccept hstop hS hside hp
    exact ⟨ht, (Finset.mem_filter.mp hS).2, hb.trans hborn.symm, hd.trans hends.symm⟩
  · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hE
    have hs := Finset.mem_toList.mp hS
    obtain ⟨ht, hb, hd⟩ := positive_terminal_is_life fixed position cutoff stop hs hpos
    exact ⟨ht, (Finset.mem_filter.mp hs).2, hb, hd⟩

noncomputable def positiveRecords (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ) :
    List (Episode V) := (records fixed position cutoff stop).filter (fun E => E.born < E.ends)

noncomputable def positiveLives (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ) :
    Finset (Set V) := ((positiveRecords fixed position cutoff stop).map Episode.anchors).toFinset

theorem positiveLives_spec (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    {S : Set V} (hS : S ∈ positiveLives fixed position cutoff stop) :
    (lifeTimes fixed position cutoff stop S).Nonempty ∧ (∀ r ∈ S, ¬ fixed r) ∧
      birth fixed position cutoff stop S < death fixed position cutoff stop S := by
  obtain ⟨E, hE, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hS)
  obtain ⟨hE, hpos⟩ := List.mem_filter.mp hE
  have hp := of_decide_eq_true hpos
  obtain ⟨ht, hr, hb, hd⟩ := positive_record_is_life fixed position cutoff stop hE hp
  exact ⟨ht, hr, by rwa [hb, hd]⟩

theorem positiveLives_product (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (hcut : cutoff ≤ stop) (p : ℝ → ℝ) (hp : ∀ t, p t ≠ 0) :
    (∏ S ∈ positiveLives fixed position cutoff stop,
      p (birth fixed position cutoff stop S) / p (death fixed position cutoff stop S)) =
      ((records fixed position cutoff stop).map (Episode.ratio p)).prod := by
  let L := records fixed position cutoff stop
  let B := positiveRecords fixed position cutoff stop
  let f : Set V → ℝ := fun S => p (birth fixed position cutoff stop S) / p (death fixed position cutoff stop S)
  have hn : (L.map Episode.anchors).Nodup :=
    allEpisodes_anchors_nodup fixed cutoff stop (length position cutoff) (execution position cutoff stop)
  have hsub : B.Sublist L := List.filter_sublist
  have hnB := hn.sublist (hsub.map Episode.anchors)
  have hz : ((L.filter (fun E => ¬ E.born < E.ends)).map (Episode.ratio p)).prod = 1 := by
    apply List.prod_eq_one
    intro r hr
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hE, hnot⟩ := List.mem_filter.mp hE
    have hle := record_nonnegative_duration fixed position cutoff stop hcut hE
    have heq : E.born = E.ends := le_antisymm hle (le_of_not_gt (of_decide_eq_true hnot))
    simp only [Episode.ratio, heq, div_self (hp E.ends)]
  calc
    _ = (B.map (fun E => f E.anchors)).prod := by
      rw [positiveLives, List.prod_toFinset f hnB, List.map_map]
      rfl
    _ = (B.map (Episode.ratio p)).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro E hE
      obtain ⟨hE, hpos⟩ := List.mem_filter.mp hE
      obtain ⟨_ht, _hr, hb, hd⟩ := positive_record_is_life fixed position cutoff stop hE (of_decide_eq_true hpos)
      simp only [f, Episode.ratio, hb, hd]
    _ = _ := by
      have h := List.prod_map_filter_mul_prod_map_filter_not (fun E : Episode V => E.born < E.ends)
        (Episode.ratio p) L
      rw [hz, mul_one] at h
      exact h

/-- Exact telescoping on the constructed finite family of actual positive
lives. All zero-length sequential lives cancel, including at tied edges. -/
theorem actual_forest_telescope (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (hcut : cutoff ≤ stop) (p : ℝ → ℝ) (hp : ∀ t, p t ≠ 0) (hstop : p stop = 1) :
    (∏ S ∈ positiveLives fixed position cutoff stop,
      p (birth fixed position cutoff stop S) / p (death fixed position cutoff stop S)) =
      p cutoff ^ Fintype.card {a // ¬ fixed a} /
        ∏ e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset,
          p (clippedEdgeLength position cutoff e) := by
  rw [positiveLives_product fixed position cutoff stop hcut p hp]
  unfold records
  rw [allEpisodes_product]
  exact terminal_sorted_ledger fixed position cutoff stop p hp hstop

theorem positiveLives_card_le (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X) (cutoff stop : ℝ) :
    (positiveLives fixed position cutoff stop).card ≤ 2*k := by
  apply ForestLifeCount.lives_card_le_twice k J fixed hroots position
  · intro S hS
    exact (positiveLives_spec fixed position cutoff stop hS).1
  · intro S hS
    exact (positiveLives_spec fixed position cutoff stop hS).2.1
  · intro S hS
    exact (positiveLives_spec fixed position cutoff stop hS).2.2

#print axioms actual_forest_telescope
#print axioms positiveLives_card_le

end ExceptionalTimes.ForestTelescope
