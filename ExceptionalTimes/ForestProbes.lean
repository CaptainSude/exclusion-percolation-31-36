import ExceptionalTimes.ForestLifeGeometry
import ExceptionalTimes.ProbeProduct

/-! Literal buffered annuli from the root-contracted Kruskal lives. The inner
radius uses the proved spanning-length upper bound for the anchor diameter. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestProbes

open RootKruskal KruskalLives ForestLifeGeometry ForestGeometry

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

noncomputable def span (fixed : V → Prop) (position : V → X) (cutoff : ℝ) (S : Set V) : ℝ :=
  ∑ e ∈ internalEdges (recorded fixed position cutoff) S, clippedEdgeLength position cutoff e

theorem span_nonneg (fixed : V → Prop) (position : V → X) (cutoff : ℝ) (S : Set V) :
    0 ≤ span fixed position cutoff S :=
  Finset.sum_nonneg (fun e _ => clippedEdgeLength_nonneg position cutoff e)

theorem dist_le_span {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ} {S : Set V}
    (htimes : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrootless : ∀ r ∈ S, ¬ fixed r) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    dist (position x) (position y) ≤ span fixed position cutoff S := by
  obtain ⟨t, ht⟩ := htimes
  exact life_distance_le_internal_sum ht.2.2 hrootless hx hy

omit [Fintype V] in
theorem lives_laminar {fixed : V → Prop} {position : V → X} {cutoff stop : ℝ} {S T : Set V}
    (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty) :
    Disjoint S T ∨ S ⊆ T ∨ T ⊆ S := by
  by_cases hd : Disjoint S T
  · exact Or.inl hd
  obtain ⟨x, hxS, hxT⟩ := Set.not_disjoint_iff.mp hd
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  obtain ⟨a, ha⟩ := hs.2.2
  obtain ⟨b, hb⟩ := ht.2.2
  rw [ha] at hxS
  rw [hb] at hxT
  rw [ha, hb]
  rcases le_total s t with hst | hts
  · exact Or.inr (Or.inl (clusters_nested_of_overlap fixed position cutoff hst hxS hxT))
  · exact Or.inr (Or.inr (clusters_nested_of_overlap fixed position cutoff hts hxT hxS))

/-- Both annular boundaries are thickened by the same microscopic margin. -/
noncomputable def buffer (fixed : V → Prop) (position : V → X) (cutoff stop margin : ℝ)
    (S : Set V) (center : V) : Set X :=
  {z | 4 * max (birth fixed position cutoff stop S) (span fixed position cutoff S + 2*margin)
      - margin ≤ dist (position center) z ∧
    dist (position center) z ≤ death fixed position cutoff stop S / 4 + margin}

theorem nested_buffers_disjoint {fixed : V → Prop} {position : V → X}
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) {S T : Set V}
    (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty)
    (hrS : ∀ r ∈ S, ¬ fixed r) (hTS : T ⊂ S)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T) :
    Disjoint (buffer fixed position cutoff stop margin S x)
      (buffer fixed position cutoff stop margin T y) := by
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  have hxy := dist_le_span hS hrS hx (hTS.1 hy)
  have hdeath := descendant_death_le_ancestor_birth hT hS hTS
  have hbirth := cutoff_le_birth hS
  have htri := dist_triangle (position x) (position y) z
  have hmax1 := le_max_left (birth fixed position cutoff stop S)
    (span fixed position cutoff S + 2*margin)
  have hmax2 := le_max_right (birth fixed position cutoff stop S)
    (span fixed position cutoff S + 2*margin)
  change _ ≤ _ ∧ _ ≤ _ at hzS hzT
  linarith [hzS.1, hzT.2]

theorem separate_buffers_disjoint {fixed : V → Prop} {position : V → X}
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : margin ≤ cutoff/100) {S T : Set V}
    (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty)
    (hlS : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (hlT : birth fixed position cutoff stop T < death fixed position cutoff stop T)
    (hdis : Disjoint S T) {x y : V} (hx : x ∈ S) (hy : y ∈ T) :
    Disjoint (buffer fixed position cutoff stop margin S x)
      (buffer fixed position cutoff stop margin T y) := by
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  have hsep := disjoint_lives_separation hS hT hlS hlT hdis hx hy
  have hbirth := cutoff_le_birth hS
  have htri := dist_triangle (position x) z (position y)
  rw [_root_.dist_comm z (position y)] at htri
  have hmax1 := le_max_left (death fixed position cutoff stop S) (death fixed position cutoff stop T)
  have hmax2 := le_max_right (death fixed position cutoff stop S) (death fixed position cutoff stop T)
  change _ ≤ _ ∧ _ ≤ _ at hzS hzT
  linarith [hzS.2, hzT.2]

/-- All different positive rootless lives have disjoint buffered probes,
including lives whose scale intervals do not overlap. -/
theorem buffers_disjoint {fixed : V → Prop} {position : V → X}
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : margin ≤ cutoff/100)
    {S T : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hT : (lifeTimes fixed position cutoff stop T).Nonempty)
    (hrS : ∀ r ∈ S, ¬ fixed r) (hrT : ∀ r ∈ T, ¬ fixed r)
    (hlS : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    (hlT : birth fixed position cutoff stop T < death fixed position cutoff stop T)
    (hne : S ≠ T) {x y : V} (hx : x ∈ S) (hy : y ∈ T) :
    Disjoint (buffer fixed position cutoff stop margin S x)
      (buffer fixed position cutoff stop margin T y) := by
  rcases lives_laminar hS hT with hd | hST | hTS
  · exact separate_buffers_disjoint hb hm hS hT hlS hlT hd hx hy
  · exact (nested_buffers_disjoint hb hT hS hrT
      (lt_of_le_of_ne hST hne) hy hx).symm
  · exact nested_buffers_disjoint hb hS hT hrS
      (lt_of_le_of_ne hTS hne.symm) hx hy

/-- A site within the microscopic support radius of any selected anchor or
physical root lies outside every buffer. -/
theorem support_not_mem_buffer {fixed : V → Prop} {position : V → X}
    {cutoff stop margin : ℝ} (hb : 0 < cutoff) (hm : margin ≤ cutoff/100)
    {S : Set V} (hS : (lifeTimes fixed position cutoff stop S).Nonempty)
    (hrS : ∀ r ∈ S, ¬ fixed r)
    (hlS : birth fixed position cutoff stop S < death fixed position cutoff stop S)
    {x : V} (hx : x ∈ S) (a : V) {z : X} (hz : dist (position a) z ≤ margin) :
    z ∉ buffer fixed position cutoff stop margin S x := by
  intro hzS
  have hbirth := cutoff_le_birth hS
  change _ ≤ _ ∧ _ ≤ _ at hzS
  by_cases ha : a ∈ S
  · have hspan := dist_le_span hS hrS hx ha
    have htri := dist_triangle (position x) (position a) z
    have hmax1 := le_max_left (birth fixed position cutoff stop S)
      (span fixed position cutoff S + 2*margin)
    have hmax2 := le_max_right (birth fixed position cutoff stop S)
      (span fixed position cutoff S + 2*margin)
    linarith [hzS.1]
  · have hsep := life_external_distance hS hlS hx ha
    have htri := dist_triangle (position x) z (position a)
    rw [_root_.dist_comm z (position a)] at htri
    linarith [hzS.2]

#print axioms buffers_disjoint
#print axioms support_not_mem_buffer

section SitePartition

variable {D A : Type*}

/-- The labels of an actual disjoint family of site sets, plus the unused sites,
are a partition of the original site set. -/
noncomputable def sitePartition (P : A → Set D)
    (hdis : Pairwise (fun a b => Disjoint (P a) (P b))) :
    ({d : D // ∀ a, d ∉ P a} ⊕ (Σ a, {d : D // d ∈ P a})) ≃ D :=
  Equiv.ofBijective (Sum.elim Subtype.val (fun s => s.2.val)) (by
    constructor
    · intro x y h
      rcases x with x | ⟨i, x⟩ <;> rcases y with y | ⟨j, y⟩
      · change x.val = y.val at h
        congr 1
        exact Subtype.ext h
      · change x.val = y.val at h
        exact False.elim (x.property j (h.symm ▸ y.property))
      · change x.val = y.val at h
        exact False.elim (y.property i (h ▸ x.property))
      · change x.val = y.val at h
        have hij : i = j := by
          by_contra hij
          exact Set.disjoint_left.mp (hdis hij) x.property (h.symm ▸ y.property)
        subst j
        congr 2
        exact Subtype.ext h
    · intro d
      by_cases hd : ∃ a, d ∈ P a
      · obtain ⟨a, ha⟩ := hd
        exact ⟨Sum.inr ⟨a, ⟨d, ha⟩⟩, rfl⟩
      · exact ⟨Sum.inl ⟨d, fun a ha => hd ⟨a, ha⟩⟩, rfl⟩)

/-- Grouping means literal restriction of the original coloring to each probe. -/
def groupColors (P : A → Set D) (ω : D → Bool) :
    ({d : D // ∀ a, d ∉ P a} → Bool) × (∀ a, {d : D // d ∈ P a} → Bool) :=
  (fun d => ω d.val, fun _ d => ω d.val)

theorem fairSites_partition [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A]
    (P : A → Set D) (hdis : Pairwise (fun a b => Disjoint (P a) (P b)))
    (f : (({d : D // ∀ a, d ∉ P a} → Bool) × (∀ a, {d : D // d ∈ P a} → Bool)) → ℝ) :
    (ProbeProduct.fairSites D).expect (fun ω => f (groupColors P ω)) =
      (ProbeProduct.probeLaw (ProbeProduct.fairSites {d : D // ∀ a, d ∉ P a})
        (fun a => ProbeProduct.fairSites {d : D // d ∈ P a})).expect f := by
  calc
    _ = (ProbeProduct.fairSites D).expect (fun ω =>
        f (ProbeProduct.splitSites (ProbeProduct.relabelColors (sitePartition P hdis).symm ω))) := rfl
    _ = _ := (ProbeProduct.fairSites_relabel (sitePartition P hdis).symm
      (fun ω => f (ProbeProduct.splitSites ω))).trans (ProbeProduct.fairSites_split_expect f)

end SitePartition

/-- Concrete lattice or other site coordinates inherit the disjoint family of
buffers produced by the forest. No independence premise is needed. -/
theorem actual_sites_pairwise {D A : Type*} (sitePosition : D → X)
    (fixed : V → Prop) (position : V → X) {cutoff stop margin : ℝ}
    (hb : 0 < cutoff) (hm : margin ≤ cutoff/100) (life : A → Set V)
    (hinj : Function.Injective life)
    (htimes : ∀ a, (lifeTimes fixed position cutoff stop (life a)).Nonempty)
    (hrootless : ∀ a, ∀ r ∈ life a, ¬ fixed r)
    (hlife : ∀ a, birth fixed position cutoff stop (life a) < death fixed position cutoff stop (life a))
    (center : A → V) (hc : ∀ a, center a ∈ life a) :
    Pairwise (fun a b => Disjoint
      (sitePosition ⁻¹' buffer fixed position cutoff stop margin (life a) (center a))
      (sitePosition ⁻¹' buffer fixed position cutoff stop margin (life b) (center b))) := by
  intro a b hab
  exact (buffers_disjoint hb hm (htimes a) (htimes b) (hrootless a) (hrootless b)
    (hlife a) (hlife b) (fun heq => hab (hinj heq)) (hc a) (hc b)).preimage sitePosition

#print axioms fairSites_partition
#print axioms actual_sites_pairwise

/-- Independence of the actual forest probes is a consequence of the original
iid site law and the proved geometry, rather than an additional assumption. -/
theorem actual_fairSites_partition {D A : Type*} [Fintype D] [DecidableEq D]
    [Fintype A] [DecidableEq A] (sitePosition : D → X)
    (fixed : V → Prop) (position : V → X) {cutoff stop margin : ℝ}
    (hb : 0 < cutoff) (hm : margin ≤ cutoff/100) (life : A → Set V)
    (hinj : Function.Injective life)
    (htimes : ∀ a, (lifeTimes fixed position cutoff stop (life a)).Nonempty)
    (hrootless : ∀ a, ∀ r ∈ life a, ¬ fixed r)
    (hlife : ∀ a, birth fixed position cutoff stop (life a) < death fixed position cutoff stop (life a))
    (center : A → V) (hc : ∀ a, center a ∈ life a)
    (f : (({d : D // ∀ a, sitePosition d ∉ buffer fixed position cutoff stop margin (life a) (center a)} → Bool) ×
      (∀ a, {d : D // sitePosition d ∈ buffer fixed position cutoff stop margin (life a) (center a)} → Bool)) → ℝ) :
    let P := fun a => sitePosition ⁻¹' buffer fixed position cutoff stop margin (life a) (center a)
    (ProbeProduct.fairSites D).expect (fun ω => f (groupColors P ω)) =
      (ProbeProduct.probeLaw (ProbeProduct.fairSites {d : D // ∀ a, d ∉ P a})
        (fun a => ProbeProduct.fairSites {d : D // d ∈ P a})).expect f := by
  exact fairSites_partition _ (actual_sites_pairwise sitePosition fixed position hb hm life hinj
    htimes hrootless hlife center hc) f

#print axioms actual_fairSites_partition

end ExceptionalTimes.ForestProbes
