import ExceptionalTimes.PolyhexCrossing

/-! Actual hexagonal facets corresponding to the two terminal rows.
The terminal contact dictionary is proved by coordinate inequalities and
convex paths inside black cells. No polygon separation input is used. -/

open Set

namespace ExceptionalTimes.PairSquareSewing

def leftFacets (u : Site) : Set (ℝ × ℝ) := {p | p ∈ HexCells.cell u ∧
  (2 * p.1 + p.2 = 2 * u.1 + u.2 - 1 ∨ p.1 - p.2 = u.1 - u.2 - 1)}

def rightFacets (u : Site) : Set (ℝ × ℝ) := {p | p ∈ HexCells.cell u ∧
  (2 * p.1 + p.2 = 2 * u.1 + u.2 + 1 ∨ p.1 - p.2 = u.1 - u.2 + 1)}

def leftPolyhexArc (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ u ∈ (axialBoxQuad n).firstSide, leftFacets u

def rightPolyhexArc (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ u ∈ (axialBoxQuad n).secondSide, rightFacets u

theorem leftFacets_coordinate {u : Site} {p : ℝ × ℝ} (h : p ∈ leftFacets u) :
    p.1 ≤ (u.1 : ℝ) - 1 / 3 := by
  obtain ⟨⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, ⟨h₅, h₆⟩⟩, heq⟩ := h
  rcases heq with h | h <;> linarith

theorem rightFacets_coordinate {u : Site} {p : ℝ × ℝ} (h : p ∈ rightFacets u) :
    (u.1 : ℝ) + 1 / 3 ≤ p.1 := by
  obtain ⟨⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, ⟨h₅, h₆⟩⟩, heq⟩ := h
  rcases heq with h | h <;> linarith

theorem leftFacets_nonempty (u : Site) : (leftFacets u).Nonempty := by
  refine ⟨((u.1 : ℝ) - 2 / 3, (u.2 : ℝ) + 1 / 3), ?_, Or.inl ?_⟩
  · dsimp [HexCells.cell]
    constructor
    · constructor <;> linarith
    · constructor <;> constructor <;> linarith
  · dsimp
    ring

theorem rightFacets_nonempty (u : Site) : (rightFacets u).Nonempty := by
  refine ⟨((u.1 : ℝ) + 2 / 3, (u.2 : ℝ) - 1 / 3), ?_, Or.inl ?_⟩
  · dsimp [HexCells.cell]
    constructor
    · constructor <;> linarith
    · constructor <;> constructor <;> linarith
  · dsimp
    ring

/-- Moving horizontally outward from a left exposed facet immediately
leaves every cell whose center is on that row or farther right. -/
theorem leftFacets_shift_excludes {u v : Site} {p : ℝ × ℝ}
    (hp : p ∈ leftFacets u) (hvu : u.1 ≤ v.1) {δ : ℝ} (hδ : 0 < δ) :
    (p.1 - δ, p.2) ∉ HexCells.cell v := by
  intro hv
  have hx := leftFacets_coordinate hp
  have hdist := (HexCells.coordinate_bounds hv).1
  rw [abs_le] at hdist
  have hlt : (v.1 : ℝ) < (u.1 : ℝ) + 1 := by dsimp at hdist; linarith
  have hlt' : v.1 < u.1 + 1 := by exact_mod_cast hlt
  have heq : v.1 = u.1 := by omega
  rcases hp with ⟨⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩, hfacet⟩
  rcases hv with ⟨⟨hd, hd'⟩, ⟨he, he'⟩, ⟨hf, hf'⟩⟩
  simp only [heq] at hd hd' he he' hf hf'
  rcases hfacet with hfacet | hfacet
  · have hy : (v.2 : ℝ) < (u.2 : ℝ) := by linarith
    have hy' : v.2 < u.2 := by exact_mod_cast hy
    have hy'' : (v.2 : ℝ) ≤ (u.2 : ℝ) - 1 := by exact_mod_cast (show v.2 ≤ u.2 - 1 by omega)
    linarith
  · have hy : (u.2 : ℝ) < (v.2 : ℝ) := by linarith
    have hy' : u.2 < v.2 := by exact_mod_cast hy
    have hy'' : (u.2 : ℝ) + 1 ≤ (v.2 : ℝ) := by exact_mod_cast (show u.2 + 1 ≤ v.2 by omega)
    linarith

theorem leftPolyhexArc_subset_polyhex (n : ℕ) : leftPolyhexArc n ⊆ polyhex n := by
  intro p hp
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hp
  exact mem_iUnion₂_of_mem (Finset.mem_filter.mp hu).1 hpu.1

theorem leftPolyhexArc_shift_outside (n : ℕ) {p : ℝ × ℝ}
    (hp : p ∈ leftPolyhexArc n) {δ : ℝ} (hδ : 0 < δ) :
    (p.1 - δ, p.2) ∉ polyhex n := by
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hp
  intro hq
  obtain ⟨v, hv, hqv⟩ := mem_iUnion₂.mp hq
  have huv : u.1 ≤ v.1 := by
    have hu' : u.1 = -(n : ℤ) := (Finset.mem_filter.mp hu).2
    rw [hu']
    simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hv
    exact hv.1.1
  exact leftFacets_shift_excludes hpu huv hδ hqv

/-- These are actual exposed boundary facets of the cell union. -/
theorem leftPolyhexArc_subset_frontier (n : ℕ) : leftPolyhexArc n ⊆ frontier (polyhex n) := by
  intro p hp
  rw [mem_frontier_iff_notMem_interior (leftPolyhexArc_subset_polyhex n hp)]
  intro hi
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hmem : (p.1 - ε / 2, p.2) ∈ Metric.ball p ε := by
    change max |(p.1 - ε / 2) - p.1| |p.2 - p.2| < ε
    have heq : (p.1 - ε / 2) - p.1 = -(ε / 2) := by ring
    rw [heq, sub_self, abs_zero, abs_neg, abs_of_pos (half_pos hε), max_eq_left (half_pos hε).le]
    linarith
  exact leftPolyhexArc_shift_outside n hp (half_pos hε) (hball hmem)

theorem rightFacets_shift_excludes {u v : Site} {p : ℝ × ℝ}
    (hp : p ∈ rightFacets u) (hvu : v.1 ≤ u.1) {δ : ℝ} (hδ : 0 < δ) :
    (p.1 + δ, p.2) ∉ HexCells.cell v := by
  intro hv
  have hx := rightFacets_coordinate hp
  have hdist := (HexCells.coordinate_bounds hv).1
  rw [abs_le] at hdist
  have hlt : (u.1 : ℝ) - 1 < (v.1 : ℝ) := by dsimp at hdist; linarith
  have hlt' : u.1 - 1 < v.1 := by exact_mod_cast hlt
  have heq : v.1 = u.1 := by omega
  rcases hp with ⟨⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩, hfacet⟩
  rcases hv with ⟨⟨hd, hd'⟩, ⟨he, he'⟩, ⟨hf, hf'⟩⟩
  simp only [heq] at hd hd' he he' hf hf'
  rcases hfacet with hfacet | hfacet
  · have hy : (u.2 : ℝ) < (v.2 : ℝ) := by linarith
    have hy' : u.2 < v.2 := by exact_mod_cast hy
    have hy'' : (u.2 : ℝ) + 1 ≤ (v.2 : ℝ) := by exact_mod_cast (show u.2 + 1 ≤ v.2 by omega)
    linarith
  · have hy : (v.2 : ℝ) < (u.2 : ℝ) := by linarith
    have hy' : v.2 < u.2 := by exact_mod_cast hy
    have hy'' : (v.2 : ℝ) ≤ (u.2 : ℝ) - 1 := by exact_mod_cast (show v.2 ≤ u.2 - 1 by omega)
    linarith

theorem rightPolyhexArc_subset_polyhex (n : ℕ) : rightPolyhexArc n ⊆ polyhex n := by
  intro p hp
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hp
  exact mem_iUnion₂_of_mem (Finset.mem_filter.mp hu).1 hpu.1

theorem rightPolyhexArc_shift_outside (n : ℕ) {p : ℝ × ℝ}
    (hp : p ∈ rightPolyhexArc n) {δ : ℝ} (hδ : 0 < δ) :
    (p.1 + δ, p.2) ∉ polyhex n := by
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hp
  intro hq
  obtain ⟨v, hv, hqv⟩ := mem_iUnion₂.mp hq
  have huv : v.1 ≤ u.1 := by
    have hu' : u.1 = (n : ℤ) := (Finset.mem_filter.mp hu).2
    rw [hu']
    simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hv
    exact hv.1.2
  exact rightFacets_shift_excludes hpu huv hδ hqv

theorem rightPolyhexArc_subset_frontier (n : ℕ) : rightPolyhexArc n ⊆ frontier (polyhex n) := by
  intro p hp
  rw [mem_frontier_iff_notMem_interior (rightPolyhexArc_subset_polyhex n hp)]
  intro hi
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hmem : (p.1 + ε / 2, p.2) ∈ Metric.ball p ε := by
    change max |(p.1 + ε / 2) - p.1| |p.2 - p.2| < ε
    have heq : (p.1 + ε / 2) - p.1 = ε / 2 := by ring
    rw [heq, sub_self, abs_zero, abs_of_pos (half_pos hε), max_eq_left (half_pos hε).le]
    linarith
  exact rightPolyhexArc_shift_outside n hp (half_pos hε) (hball hmem)

/-- The exposed left side never folds back to a second point at the
same height. This gives a concrete no-self-intersection certificate. -/
theorem leftPolyhexArc_snd_injective (n : ℕ) : Set.InjOn Prod.snd (leftPolyhexArc n) := by
  have never_left (a b : ℝ × ℝ) (ha : a ∈ leftPolyhexArc n) (hb : b ∈ leftPolyhexArc n)
      (hy : a.2 = b.2) : ¬ a.1 < b.1 := by
    intro hlt
    have hout := leftPolyhexArc_shift_outside n hb (sub_pos.mpr hlt)
    have heq : (b.1 - (b.1 - a.1), b.2) = a := by
      apply Prod.ext
      · dsimp
        ring
      · exact hy.symm
    rw [heq] at hout
    exact hout (leftPolyhexArc_subset_polyhex n ha)
  intro a ha b hb hy
  exact Prod.ext (le_antisymm (not_lt.mp (never_left b a hb ha hy.symm))
    (not_lt.mp (never_left a b ha hb hy))) hy

theorem rightPolyhexArc_snd_injective (n : ℕ) : Set.InjOn Prod.snd (rightPolyhexArc n) := by
  have never_right (a b : ℝ × ℝ) (ha : a ∈ rightPolyhexArc n) (hb : b ∈ rightPolyhexArc n)
      (hy : a.2 = b.2) : ¬ b.1 < a.1 := by
    intro hlt
    have hout := rightPolyhexArc_shift_outside n hb (sub_pos.mpr hlt)
    have heq : (b.1 + (a.1 - b.1), b.2) = a := by
      apply Prod.ext
      · dsimp
        ring
      · exact hy.symm
    rw [heq] at hout
    exact hout (rightPolyhexArc_subset_polyhex n ha)
  intro a ha b hb hy
  exact Prod.ext (le_antisymm (not_lt.mp (never_right a b ha hb hy))
    (not_lt.mp (never_right b a hb ha hy.symm))) hy

/-- Even a contact at a shared cell vertex cannot create a spurious
left-terminal black cell: every in-domain cell touching the left arc
has its center on the actual left terminal row. -/
theorem leftArc_cell_in_firstSide (n : ℕ) {p : ℝ × ℝ} {v : Site}
    (hp : p ∈ leftPolyhexArc n) (hv : v ∈ (axialBoxQuad n).domain)
    (hpv : p ∈ HexCells.cell v) : v ∈ (axialBoxQuad n).firstSide := by
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hp
  have hu' : u.1 = -(n : ℤ) := (Finset.mem_filter.mp hu).2
  have hx := leftFacets_coordinate hpu
  have hvx := (HexCells.coordinate_bounds hpv).1
  rw [abs_le] at hvx
  have hlt : (v.1 : ℝ) < -(n : ℝ) + 1 := by
    rw [hu'] at hx
    push_cast at hx
    linarith
  have hlt' : v.1 < -(n : ℤ) + 1 := by exact_mod_cast hlt
  have hvbox := hv
  change v ∈ latticeBox n at hvbox
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hvbox
  have heq : v.1 = -(n : ℤ) := by omega
  exact Finset.mem_filter.mpr ⟨hv, heq⟩

theorem rightArc_cell_in_secondSide (n : ℕ) {p : ℝ × ℝ} {v : Site}
    (hp : p ∈ rightPolyhexArc n) (hv : v ∈ (axialBoxQuad n).domain)
    (hpv : p ∈ HexCells.cell v) : v ∈ (axialBoxQuad n).secondSide := by
  obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hp
  have hu' : u.1 = (n : ℤ) := (Finset.mem_filter.mp hu).2
  have hx := rightFacets_coordinate hpu
  have hvx := (HexCells.coordinate_bounds hpv).1
  rw [abs_le] at hvx
  have hlt : (n : ℝ) - 1 < (v.1 : ℝ) := by
    rw [hu'] at hx
    push_cast at hx
    linarith
  have hlt' : (n : ℤ) - 1 < v.1 := by exact_mod_cast hlt
  have hvbox := hv
  change v ∈ latticeBox n at hvbox
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hvbox
  have heq : v.1 = (n : ℤ) := by omega
  exact Finset.mem_filter.mpr ⟨hv, heq⟩

def PolyhexArcCrossing (n : ℕ) (ω : Configuration) : Prop :=
  ∃ a ∈ leftPolyhexArc n, ∃ b ∈ rightPolyhexArc n,
    JoinedIn (blackCellUnion HexCells.cell (axialBoxQuad n) ω) a b

theorem polyhexArcCrossing_to_cellPathCrossing (n : ℕ) (ω : Configuration)
    (h : PolyhexArcCrossing n ω) : CellPathCrossing HexCells.cell (axialBoxQuad n) ω := by
  obtain ⟨a, ha, b, hb, hj⟩ := h
  obtain ⟨u, huD, huB, hau⟩ := hj.source_mem
  obtain ⟨v, hvD, hvB, hbv⟩ := hj.target_mem
  exact ⟨u, leftArc_cell_in_firstSide n ha huD hau, huD, huB,
    v, rightArc_cell_in_secondSide n hb hvD hbv, hvD, hvB, a, hau, b, hbv, hj⟩

theorem cellPathCrossing_to_polyhexArcCrossing (n : ℕ) (ω : Configuration)
    (h : CellPathCrossing HexCells.cell (axialBoxQuad n) ω) : PolyhexArcCrossing n ω := by
  obtain ⟨u, hu, huD, huB, v, hv, hvD, hvB, a, ha, b, hb, hj⟩ := h
  obtain ⟨a', ha'⟩ := leftFacets_nonempty u
  obtain ⟨b', hb'⟩ := rightFacets_nonempty v
  have hcu := (HexCells.convex_cell u).isPathConnected ⟨a, ha⟩
  have hcv := (HexCells.convex_cell v).isPathConnected ⟨b, hb⟩
  have hua : JoinedIn (blackCellUnion HexCells.cell (axialBoxQuad n) ω) a' a :=
    (hcu.joinedIn a' ha'.1 a ha).mono (fun _ hp => ⟨u, huD, huB, hp⟩)
  have hvb : JoinedIn (blackCellUnion HexCells.cell (axialBoxQuad n) ω) b b' :=
    (hcv.joinedIn b hb b' hb'.1).mono (fun _ hp => ⟨v, hvD, hvB, hp⟩)
  exact ⟨a', mem_iUnion₂_of_mem hu ha', b', mem_iUnion₂_of_mem hv hb',
    (hua.trans hj).trans hvb⟩

/-- Actual continuous black closed-cell crossings between the explicit
left/right polygonal facets equal the original graph crossing. This
removes the terminal-row dictionary without assuming any planar theorem. -/
theorem axialBox_graphCrossing_iff_arcCrossing (n : ℕ) (ω : Configuration) :
    (axialBoxQuad n).Crossing ω ↔ PolyhexArcCrossing n ω := by
  rw [axialBox_graphCrossing_iff_cellPathCrossing]
  exact ⟨cellPathCrossing_to_polyhexArcCrossing n ω, polyhexArcCrossing_to_cellPathCrossing n ω⟩

#print axioms leftArc_cell_in_firstSide
#print axioms leftPolyhexArc_subset_frontier
#print axioms rightPolyhexArc_subset_frontier
#print axioms axialBox_graphCrossing_iff_arcCrossing

end ExceptionalTimes.PairSquareSewing
