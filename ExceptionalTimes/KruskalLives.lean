import ExceptionalTimes.RootKruskal

/-! Birth and death scales are constructed from actual occurrences of a
root-contracted threshold component. Their interval and separation properties
are proved from graph connectivity, rather than assumed as life certificates. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.KruskalLives

open RootKruskal

variable {V X : Type*} [PseudoMetricSpace X]

def Occurs (fixed : V → Prop) (position : V → X) (cutoff : ℝ) (S : Set V) (t : ℝ) : Prop :=
  ∃ a, S = cluster fixed position cutoff t a

def lifeTimes (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ) (S : Set V) : Set ℝ :=
  {t | cutoff ≤ t ∧ t ≤ stop ∧ Occurs fixed position cutoff S t}

noncomputable def birth (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ) (S : Set V) : ℝ :=
  sInf (lifeTimes fixed position cutoff stop S)

noncomputable def death (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ) (S : Set V) : ℝ :=
  sSup (lifeTimes fixed position cutoff stop S)

theorem occurs_nonempty {fixed : V → Prop} {position : V → X} {cutoff t : ℝ} {S : Set V}
    (h : Occurs fixed position cutoff S t) : S.Nonempty := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a, cluster_self fixed position cutoff t a⟩

theorem occurs_eq_of_overlap {fixed : V → Prop} {position : V → X} {cutoff t : ℝ}
    {S T : Set V} (hS : Occurs fixed position cutoff S t) (hT : Occurs fixed position cutoff T t)
    {x : V} (hxS : x ∈ S) (hxT : x ∈ T) : S = T := by
  obtain ⟨a, rfl⟩ := hS
  obtain ⟨b, rfl⟩ := hT
  exact Set.Subset.antisymm
    (clusters_nested_of_overlap fixed position cutoff le_rfl hxS hxT)
    (clusters_nested_of_overlap fixed position cutoff le_rfl hxT hxS)

theorem occurs_between {fixed : V → Prop} {position : V → X} {cutoff s t r : ℝ}
    {S : Set V} (hs : Occurs fixed position cutoff S s) (ht : Occurs fixed position cutoff S t)
    (hsr : s ≤ r) (hrt : r ≤ t) : Occurs fixed position cutoff S r := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  have haS : a ∈ S := ha.symm ▸ cluster_self fixed position cutoff s a
  have hat : a ∈ cluster fixed position cutoff t b := hb ▸ haS
  refine ⟨a, Set.Subset.antisymm ?_ ?_⟩
  · rw [ha]
    exact clusters_nested_of_overlap fixed position cutoff hsr
      (cluster_self fixed position cutoff s a) (cluster_self fixed position cutoff r a)
  · rw [hb]
    exact clusters_nested_of_overlap fixed position cutoff hrt
      (cluster_self fixed position cutoff r a) hat

/-- Every scale strictly between the constructed endpoints belongs to this
component's actual occurrence set; components cannot disappear and reappear. -/
theorem interior_mem_lifeTimes {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ}
    {S : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty) {t : ℝ}
    (hbt : birth fixed position cutoff stop S < t) (htd : t < death fixed position cutoff stop S) :
    t ∈ lifeTimes fixed position cutoff stop S := by
  obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hS hbt
  obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup hS htd
  exact ⟨hs.1.trans hst.le, htr.le.trans hr.2.1,
    occurs_between hs.2.2 hr.2.2 hst.le htr.le⟩

theorem cutoff_le_birth {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ}
    {S : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty) :
    cutoff ≤ birth fixed position cutoff stop S :=
  le_csInf hS (fun _ h => h.1)

theorem death_le_stop {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ}
    {S : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty) :
    death fixed position cutoff stop S ≤ stop :=
  csSup_le hS (fun _ h => h.2.1)

/-- The full life separation property holds against every exterior point,
including points belonging to lives with disjoint scale intervals. -/
theorem life_external_distance {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ}
    {S : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hlife : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    {x y : V} (hx : x ∈ S) (hy : y ∉ S) :
    death fixed position cutoff stop S ≤ dist (position x) (position y) := by
  have hsep : death fixed position cutoff stop S ≤ max (dist (position x) (position y)) cutoff := by
    apply csSup_le hS
    intro t ht
    obtain ⟨a, ha⟩ := ht.2.2
    exact cluster_external_separation fixed position cutoff t (ha ▸ hx) (ha ▸ hy)
  exact (le_max_iff.mp hsep).resolve_right
    (not_le.mpr ((cutoff_le_birth hS).trans_lt hlife))

theorem disjoint_lives_separation {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ}
    {S T : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty)
    (hlS : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (hlT : birth fixed position cutoff stop T < death fixed position cutoff stop T)
    (hdis : Disjoint S T) {x y : V} (hx : x ∈ S) (hy : y ∈ T) :
    max (death fixed position cutoff stop S) (death fixed position cutoff stop T) ≤
      dist (position x) (position y) := by
  apply max_le
  · exact life_external_distance hS hlS hx (fun hyS => Set.disjoint_left.mp hdis hyS hy)
  · simpa only [dist_comm] using life_external_distance hT hlT hy
      (fun hxT => Set.disjoint_left.mp hdis hx hxT)

/-- A strict ancestor starts only after its descendant has ended. This proves
the disjoint scale intervals needed when charging any internal edge along its
ancestor chain. -/
theorem descendant_death_le_ancestor_birth {fixed : V → Prop} {position : V → X}
    {cutoff stop : ℝ} {S T : Set V}
    (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty) (hST : S ⊂ T) :
    death fixed position cutoff stop S ≤ birth fixed position cutoff stop T := by
  apply le_csInf hT
  intro t ht
  apply csSup_le hS
  intro s hs
  by_contra hts
  have hts' : t ≤ s := (lt_of_not_ge hts).le
  obtain ⟨x, hx⟩ := occurs_nonempty hs.2.2
  obtain ⟨a, ha⟩ := hs.2.2
  obtain ⟨b, hb⟩ := ht.2.2
  have hsub : T ⊆ S := by
    rw [ha, hb]
    exact clusters_nested_of_overlap fixed position cutoff hts' (hb ▸ hST.1 hx) (ha ▸ hx)
  exact hST.2 hsub

/-- At a given scale, two distinct lives sharing even one anchor cannot both
be active. In particular an internal edge is never charged twice at that scale. -/
theorem active_lives_unique {fixed : V → Prop} {position : V → X} {cutoff stop t : ℝ}
    {S T : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty)
    (htS : birth fixed position cutoff stop S < t ∧ t < death fixed position cutoff stop S)
    (htT : birth fixed position cutoff stop T < t ∧ t < death fixed position cutoff stop T)
    {x : V} (hxS : x ∈ S) (hxT : x ∈ T) : S = T :=
  occurs_eq_of_overlap (interior_mem_lifeTimes hS htS.1 htS.2).2.2
    (interior_mem_lifeTimes hT htT.1 htT.2).2.2 hxS hxT

#print axioms interior_mem_lifeTimes
#print axioms life_external_distance
#print axioms disjoint_lives_separation
#print axioms descendant_death_le_ancestor_birth
#print axioms active_lives_unique

end ExceptionalTimes.KruskalLives


