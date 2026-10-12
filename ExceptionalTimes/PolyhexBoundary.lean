import ExceptionalTimes.PolyhexArcs

open Set

namespace ExceptionalTimes.PairSquareSewing

theorem polyhex_coordinate_bounds {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ polyhex n) :
    -(n : ℝ)-2/3 ≤ p.1 ∧ p.1 ≤ (n : ℝ)+2/3 ∧
    -(n : ℝ)-2/3 ≤ p.2 ∧ p.2 ≤ (n : ℝ)+2/3 := by
  obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hu
  have hb := HexCells.coordinate_bounds hpu
  rw [abs_le, abs_le] at hb
  have h1 : -(n : ℝ) ≤ (u.1 : ℝ) := by exact_mod_cast hu.1.1
  have h2 : (u.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hu.1.2
  have h3 : -(n : ℝ) ≤ (u.2 : ℝ) := by exact_mod_cast hu.2.1
  have h4 : (u.2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hu.2.2
  repeat' constructor
  all_goals linarith [hb.1.1,hb.1.2,hb.2.1,hb.2.2]

theorem near_polyhex_cell_in_box {n : ℕ} {p q : ℝ × ℝ} {u : Site}
    (hp : p ∈ polyhex n) (hq : q ∈ Metric.ball p 1) (hu : q ∈ HexCells.cell u) :
    u ∈ latticeBox (n+3) := by
  have hb := polyhex_coordinate_bounds hp
  have hc := HexCells.coordinate_bounds hu
  rw [abs_le, abs_le] at hc
  have hd : max |q.1-p.1| |q.2-p.2| < 1 := hq
  have hd1 := (abs_lt.mp ((le_max_left _ _).trans_lt hd))
  have hd2 := (abs_lt.mp ((le_max_right _ _).trans_lt hd))
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  have h1 : -(n : ℝ)-3 ≤ (u.1 : ℝ) := by linarith [hb.1,hc.1.2]
  have h2 : (u.1 : ℝ) ≤ (n : ℝ)+3 := by linarith [hb.2.1,hc.1.1]
  have h3 : -(n : ℝ)-3 ≤ (u.2 : ℝ) := by linarith [hb.2.2.1,hc.2.2]
  have h4 : (u.2 : ℝ) ≤ (n : ℝ)+3 := by linarith [hb.2.2.2,hc.2.1]
  constructor <;> constructor
  · have h1' : -(n : ℤ)-3 ≤ u.1 := by exact_mod_cast h1
    omega
  · exact_mod_cast h2
  · have h3' : -(n : ℤ)-3 ≤ u.2 := by exact_mod_cast h3
    omega
  · exact_mod_cast h4

/-- An actual boundary point touches a cell excluded from the board.
This uses the proved full-plane tiling and an explicit finite local cover. -/
theorem frontier_touches_outside_cell (n : ℕ) {p : ℝ × ℝ}
    (hp : p ∈ frontier (polyhex n)) :
    ∃ u : Site, u ∉ latticeBox n ∧ p ∈ HexCells.cell u := by
  have hpin : p ∈ polyhex n := (polyhex_isCompact n).isClosed.closure_eq ▸ frontier_subset_closure hp
  by_contra! h
  let V : Set (ℝ × ℝ) := ⋃ u ∈ (latticeBox (n+3) \ latticeBox n), HexCells.cell u
  have hV : IsClosed V := ((latticeBox (n+3) \ latticeBox n).isCompact_biUnion
    (fun u _ => HexCells.isCompact_cell u)).isClosed
  have hpV : p ∉ V := by
    intro hpV
    obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hpV
    exact h u (Finset.mem_sdiff.mp hu).2 hpu
  have hnhds := Filter.inter_mem (Metric.ball_mem_nhds p (by norm_num : (0 : ℝ)<1))
    (hV.compl_mem_nhds hpV)
  have hsub : Metric.ball p 1 ∩ Vᶜ ⊆ polyhex n := by
    intro q hq
    obtain ⟨u,hu⟩ := HexTiling.plane_covered q
    have hubox := near_polyhex_cell_in_box hpin hq.1 hu
    have huin : u ∈ latticeBox n := by
      by_contra hout
      exact hq.2 (mem_iUnion₂_of_mem (Finset.mem_sdiff.mpr ⟨hubox,hout⟩) hu)
    exact mem_iUnion₂_of_mem huin hu
  have hi := mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hnhds hsub)
  exact (mem_frontier_iff_notMem_interior hpin).mp hp hi

theorem common_cell_leftFacets {u v : Site} {p : ℝ × ℝ}
    (hpu : p ∈ HexCells.cell u) (hpv : p ∈ HexCells.cell v) (hx : v.1 < u.1) :
    p ∈ leftFacets u := by
  refine ⟨hpu,?_⟩
  have hadj := HexCells.intersection_only_neighbors hpu hpv
  rcases hadj with rfl | hadj
  · omega
  rcases hadj with h | h | h | h | h | h
  all_goals rcases h with ⟨h1,h2⟩
  all_goals try omega
  · apply Or.inl
    rw [HexCells.cell] at hpu hpv
    simp only [mem_ofPred, mem_Icc] at hpu hpv
    rw [h1,h2] at hpv
    push_cast at hpv
    linarith [hpu.1.1,hpv.1.2]
  · apply Or.inr
    rw [HexCells.cell] at hpu hpv
    simp only [mem_ofPred, mem_Icc] at hpu hpv
    rw [h1,h2] at hpv
    push_cast at hpv
    linarith [hpu.2.2.1,hpv.2.2.2]

theorem common_cell_rightFacets {u v : Site} {p : ℝ × ℝ}
    (hpu : p ∈ HexCells.cell u) (hpv : p ∈ HexCells.cell v) (hx : u.1 < v.1) :
    p ∈ rightFacets u := by
  have h := common_cell_leftFacets ((neg_mem_hexCell_iff u p).mpr hpu)
    ((neg_mem_hexCell_iff v p).mpr hpv) (by change -v.1 < -u.1; omega)
  have hh := (neg_mem_rightFacets_iff (-u) (-p)).mpr h
  simpa only [neg_neg] using hh

theorem polyhex_frontier_subset_rawArcs (n : ℕ) :
    frontier (polyhex n) ⊆ leftPolyhexArc n ∪ rightPolyhexArc n ∪
      topPolyhexRawArc n ∪ bottomPolyhexRawArc n := by
  intro p hp
  have hpin : p ∈ polyhex n := (polyhex_isCompact n).isClosed.closure_eq ▸ frontier_subset_closure hp
  obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hpin
  obtain ⟨v,hv,hpv⟩ := frontier_touches_outside_cell n hp
  have huB := hu
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at huB hv
  have hadj : TriangularAdj u v := by
    rcases HexCells.intersection_only_neighbors hpu hpv with heq | h
    · subst v
      exact False.elim (hv huB)
    · exact h
  have hcoord : u.1-1 ≤ v.1 ∧ v.1 ≤ u.1+1 ∧ u.2-1 ≤ v.2 ∧ v.2 ≤ u.2+1 := by
    unfold TriangularAdj at hadj
    omega
  by_cases hl : v.1 < -(n : ℤ)
  · have heq : u.1 = -(n : ℤ) := by omega
    apply Or.inl ∘ Or.inl ∘ Or.inl
    exact mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hu,heq⟩)
      (common_cell_leftFacets hpu hpv (by omega))
  by_cases hr : (n : ℤ) < v.1
  · have heq : u.1 = (n : ℤ) := by omega
    apply Or.inl ∘ Or.inl ∘ Or.inr
    exact mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hu,heq⟩)
      (common_cell_rightFacets hpu hpv (by omega))
  by_cases hb : v.2 < -(n : ℤ)
  · have heq : u.2 = -(n : ℤ) := by omega
    apply Or.inr
    refine ⟨p.swap,?_,Prod.swap_swap p⟩
    exact mem_iUnion₂_of_mem (i := u.swap)
      (Finset.mem_filter.mpr ⟨(swap_mem_latticeBox_iff n u).mpr hu,heq⟩)
      (common_cell_leftFacets ((swap_mem_hexCell_iff u p).mpr hpu)
        ((swap_mem_hexCell_iff v p).mpr hpv) (by change v.2 < u.2; omega))
  · have heq : u.2 = (n : ℤ) := by omega
    apply Or.inl ∘ Or.inr
    refine ⟨p.swap,?_,Prod.swap_swap p⟩
    exact mem_iUnion₂_of_mem (i := u.swap)
      (Finset.mem_filter.mpr ⟨(swap_mem_latticeBox_iff n u).mpr hu,heq⟩)
      (common_cell_rightFacets ((swap_mem_hexCell_iff u p).mpr hpu)
        ((swap_mem_hexCell_iff v p).mpr hpv) (by change u.2 < v.2; omega))

theorem swap_polyhex (n : ℕ) : Prod.swap '' polyhex n = polyhex n := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (swap_mem_polyhex_iff n q).mpr hq
  · intro hp
    exact ⟨p.swap,(swap_mem_polyhex_iff n p).mpr hp,Prod.swap_swap p⟩

theorem swap_polyhex_frontier (n : ℕ) :
    Prod.swap '' frontier (polyhex n) = frontier (polyhex n) := by
  have h := (Homeomorph.prodComm ℝ ℝ).image_frontier (polyhex n)
  change Prod.swap '' frontier (polyhex n) = frontier (Prod.swap '' polyhex n) at h
  rwa [swap_polyhex] at h

theorem topPolyhexRawArc_subset_frontier (n : ℕ) :
    topPolyhexRawArc n ⊆ frontier (polyhex n) := by
  rintro p ⟨q,hq,rfl⟩
  rw [← swap_polyhex_frontier]
  exact ⟨q,rightPolyhexArc_subset_frontier n hq,rfl⟩

theorem bottomPolyhexRawArc_subset_frontier (n : ℕ) :
    bottomPolyhexRawArc n ⊆ frontier (polyhex n) := by
  rintro p ⟨q,hq,rfl⟩
  rw [← swap_polyhex_frontier]
  exact ⟨q,leftPolyhexArc_subset_frontier n hq,rfl⟩

/-- Exact boundary equality for the full finite cell union. The raw
upper and lower arcs overlap the neighboring sides by one corner facet. -/
theorem polyhex_frontier_eq_rawArcs (n : ℕ) :
    frontier (polyhex n) = leftPolyhexArc n ∪ rightPolyhexArc n ∪
      topPolyhexRawArc n ∪ bottomPolyhexRawArc n := by
  apply subset_antisymm (polyhex_frontier_subset_rawArcs n)
  exact union_subset (union_subset (union_subset (leftPolyhexArc_subset_frontier n)
    (rightPolyhexArc_subset_frontier n)) (topPolyhexRawArc_subset_frontier n))
    (bottomPolyhexRawArc_subset_frontier n)

theorem leftArc_truncate_preconnected (n : ℕ) {b : ℝ}
    (hb : b ∈ Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3)) :
    IsPreconnected (leftPolyhexArc n ∩ {p | p.2 ≤ b}) := by
  let inc : ↥(Icc (-(n : ℝ)-1/3) b) → ↥(Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3)) :=
    fun y => ⟨y.val,⟨y.property.1,y.property.2.trans hb.2⟩⟩
  let g : ↥(Icc (-(n : ℝ)-1/3) b) → ℝ × ℝ :=
    fun y => ((leftPolyhexArcHomeomorph n).symm (inc y)).val
  have hg : Continuous g := continuous_subtype_val.comp
    ((leftPolyhexArcHomeomorph n).symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  have heq : range g = leftPolyhexArc n ∩ {p | p.2 ≤ b} := by
    ext p
    constructor
    · rintro ⟨y,rfl⟩
      refine ⟨((leftPolyhexArcHomeomorph n).symm (inc y)).property,?_⟩
      have hy := congrArg Subtype.val ((leftPolyhexArcHomeomorph n).apply_symm_apply (inc y))
      change (g y).2 = y.val at hy
      change (g y).2 ≤ b
      rw [hy]
      exact y.property.2
    · rintro ⟨hp,hpb⟩
      have hpheight : p.2 ∈ Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3) := by
        rw [← leftPolyhexArc_height_image]
        exact ⟨p,hp,rfl⟩
      refine ⟨⟨p.2,⟨hpheight.1,hpb⟩⟩,?_⟩
      change ((leftPolyhexArcHomeomorph n).symm
        ((leftPolyhexArcHomeomorph n) ⟨p,hp⟩)).val = p
      rw [Homeomorph.symm_apply_apply]
  rw [← heq]
  let : PreconnectedSpace ↥(Icc (-(n : ℝ)-1/3) b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact isPreconnected_range hg

def topPolyhexArc (n : ℕ) : Set (ℝ × ℝ) :=
  topPolyhexRawArc n ∩ {p | -(n : ℝ)-1/3 ≤ p.1}

def bottomPolyhexArc (n : ℕ) : Set (ℝ × ℝ) := Neg.neg '' topPolyhexArc n

theorem topPolyhexArc_eq_image_truncate (n : ℕ) :
    topPolyhexArc n = (fun p : ℝ × ℝ => (-p).swap) ''
      (leftPolyhexArc n ∩ {p | p.2 ≤ (n : ℝ)+1/3}) := by
  ext p
  constructor
  · rintro ⟨⟨q,hq,rfl⟩,hb⟩
    refine ⟨-q,⟨?_,?_⟩,by simp only [neg_neg]⟩
    · exact (neg_mem_rightPolyhexArc_iff n (-q)).mp (by simpa only [neg_neg] using hq)
    · change -q.2 ≤ (n : ℝ)+1/3
      change -(n : ℝ)-1/3 ≤ q.2 at hb
      linarith
  · rintro ⟨q,⟨hq,hb⟩,rfl⟩
    refine ⟨⟨-q,(neg_mem_rightPolyhexArc_iff n q).mpr hq,rfl⟩,?_⟩
    change -(n : ℝ)-1/3 ≤ -q.2
    change q.2 ≤ (n : ℝ)+1/3 at hb
    linarith

theorem topPolyhexArc_preconnected (n : ℕ) : IsPreconnected (topPolyhexArc n) := by
  rw [topPolyhexArc_eq_image_truncate]
  apply IsPreconnected.image _ _ (continuous_swap.comp continuous_neg).continuousOn
  apply leftArc_truncate_preconnected
  constructor <;> linarith [show (0 : ℝ) ≤ n by positivity]

theorem topPolyhexArc_isCompact (n : ℕ) : IsCompact (topPolyhexArc n) :=
  (topPolyhexRawArc_isCompact n).of_isClosed_subset
    ((topPolyhexRawArc_isCompact n).isClosed.inter (isClosed_le continuous_const continuous_fst))
    inter_subset_left

theorem bottomPolyhexArc_preconnected (n : ℕ) : IsPreconnected (bottomPolyhexArc n) :=
  (topPolyhexArc_preconnected n).image Neg.neg continuous_neg.continuousOn

theorem bottomPolyhexArc_isCompact (n : ℕ) : IsCompact (bottomPolyhexArc n) :=
  (topPolyhexArc_isCompact n).image continuous_neg

theorem topRaw_left_tail {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ topPolyhexRawArc n)
    (hx : p.1 < -(n : ℝ)-1/3) : p ∈ leftPolyhexArc n := by
  obtain ⟨q,hq,rfl⟩ := hp
  obtain ⟨u,hu,hqu⟩ := mem_iUnion₂.mp hq
  obtain ⟨huD,hux⟩ := Finset.mem_filter.mp hu
  have huB := huD
  change u ∈ latticeBox n at huB
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at huB
  have hbound := (HexCells.coordinate_bounds hqu.1).2
  rw [abs_le] at hbound
  have hylt : (u.2 : ℝ) < -(n : ℝ)+1 := by change q.2 < _ at hx; linarith
  have hylt' : u.2 < -(n : ℤ)+1 := by exact_mod_cast hylt
  have huy : u.2 = -(n : ℤ) := by omega
  refine mem_iUnion₂_of_mem (i := u.swap)
    (Finset.mem_filter.mpr ⟨(swap_mem_latticeBox_iff n u).mpr huD,huy⟩) ?_
  refine ⟨(swap_mem_hexCell_iff u q).mpr hqu.1,Or.inr ?_⟩
  rcases hqu with ⟨⟨⟨ha,ha'⟩,⟨hb,hb'⟩,⟨hc,hc'⟩⟩,h | h⟩
  · change q.2-q.1 = (u.2 : ℝ)-(u.1 : ℝ)-1
    have huyR : (u.2 : ℝ) = -(n : ℝ) := by exact_mod_cast huy
    change q.2 < _ at hx
    exfalso
    linarith
  · change q.2-q.1 = (u.2 : ℝ)-(u.1 : ℝ)-1
    linarith

theorem neg_mem_bottomRaw_iff (n : ℕ) (p : ℝ × ℝ) :
    -p ∈ bottomPolyhexRawArc n ↔ p ∈ topPolyhexRawArc n := by
  constructor
  · rintro ⟨q,hq,heq⟩
    refine ⟨-q,(neg_mem_rightPolyhexArc_iff n q).mpr hq,?_⟩
    have h := congrArg Neg.neg heq
    have he : (-q).swap = -q.swap := by ext <;> rfl
    rw [he]
    simpa only [neg_neg] using h
  · rintro ⟨q,hq,rfl⟩
    exact ⟨-q,(neg_mem_rightPolyhexArc_iff n (-q)).mp (by simpa only [neg_neg] using hq),rfl⟩

theorem bottomPolyhexArc_subset_raw (n : ℕ) : bottomPolyhexArc n ⊆ bottomPolyhexRawArc n := by
  rintro p ⟨q,hq,rfl⟩
  exact (neg_mem_bottomRaw_iff n q).mpr hq.1

theorem polyhex_frontier_eq_arcs (n : ℕ) :
    frontier (polyhex n) = leftPolyhexArc n ∪ rightPolyhexArc n ∪
      topPolyhexArc n ∪ bottomPolyhexArc n := by
  apply subset_antisymm
  · intro p hp
    rw [polyhex_frontier_eq_rawArcs] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · exact Or.inl (Or.inl (Or.inl hp))
    · exact Or.inl (Or.inl (Or.inr hp))
    · by_cases hx : -(n : ℝ)-1/3 ≤ p.1
      · exact Or.inl (Or.inr ⟨hp,hx⟩)
      · exact Or.inl (Or.inl (Or.inl (topRaw_left_tail hp (lt_of_not_ge hx))))
    · have hp' : -p ∈ topPolyhexRawArc n :=
        (neg_mem_bottomRaw_iff n (-p)).mp (by simpa only [neg_neg] using hp)
      by_cases hx : -(n : ℝ)-1/3 ≤ (-p).1
      · exact Or.inr ⟨-p,⟨hp',hx⟩,neg_neg p⟩
      · have hl := topRaw_left_tail hp' (lt_of_not_ge hx)
        have hr := (neg_mem_rightPolyhexArc_iff n (-p)).mpr hl
        exact Or.inl (Or.inl (Or.inr (by simpa only [neg_neg] using hr)))
  · exact union_subset (union_subset (union_subset (leftPolyhexArc_subset_frontier n)
      (rightPolyhexArc_subset_frontier n))
      (fun _ hp => topPolyhexRawArc_subset_frontier n hp.1))
      (fun _ hp => bottomPolyhexRawArc_subset_frontier n (bottomPolyhexArc_subset_raw n hp))

theorem leftArc_x_bound {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ leftPolyhexArc n) :
    p.1 ≤ -(n : ℝ)-1/3 := by
  obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
  have h := leftFacets_coordinate hpu
  rw [(Finset.mem_filter.mp hu).2] at h
  simpa only [Int.cast_neg,Int.cast_natCast] using h

theorem rightArc_x_bound {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ rightPolyhexArc n) :
    (n : ℝ)+1/3 ≤ p.1 := by
  obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
  have h := rightFacets_coordinate hpu
  rw [(Finset.mem_filter.mp hu).2] at h
  simpa only [Int.cast_natCast] using h

theorem topArc_y_bound {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ topPolyhexArc n) :
    (n : ℝ)+1/3 ≤ p.2 := by
  obtain ⟨q,hq,heq⟩ := hp.1
  subst p
  exact rightArc_x_bound hq

theorem bottomArc_y_bound {n : ℕ} {p : ℝ × ℝ} (hp : p ∈ bottomPolyhexArc n) :
    p.2 ≤ -(n : ℝ)-1/3 := by
  obtain ⟨q,hq,rfl⟩ := hp
  have h := topArc_y_bound hq
  change -q.2 ≤ -(n : ℝ)-1/3
  linarith

noncomputable def upperRight (n : ℕ) : ℝ × ℝ := -lowerLeft n
noncomputable def lowerRight (n : ℕ) : ℝ × ℝ := -upperLeft n

theorem upperRight_mem (n : ℕ) : upperRight n ∈ rightPolyhexArc n :=
  (neg_mem_rightPolyhexArc_iff n (lowerLeft n)).mpr (lowerLeft_mem n)

theorem lowerRight_mem (n : ℕ) : lowerRight n ∈ rightPolyhexArc n :=
  (neg_mem_rightPolyhexArc_iff n (upperLeft n)).mpr (upperLeft_mem n)

theorem upperLeft_mem_top (n : ℕ) : upperLeft n ∈ topPolyhexArc n := by
  refine ⟨⟨(upperLeft n).swap,?_,Prod.swap_swap _⟩,by dsimp [upperLeft]; rfl⟩
  refine mem_iUnion₂_of_mem (i := ((n : ℤ),-(n : ℤ))) ?_ ?_
  · change ((n : ℤ),-(n : ℤ)) ∈ (latticeBox n).filter (fun u => u.1 = (n : ℤ))
    simp only [Finset.mem_filter,latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
    exact ⟨⟨⟨by omega,le_rfl⟩,⟨le_rfl,by omega⟩⟩,trivial⟩
  · refine ⟨?_,Or.inl ?_⟩
    · dsimp [HexCells.cell,upperLeft]
      push_cast
      repeat' constructor
      all_goals linarith
    · dsimp [upperLeft]
      push_cast
      ring

theorem upperRight_mem_top (n : ℕ) : upperRight n ∈ topPolyhexArc n := by
  refine ⟨⟨upperRight n,upperRight_mem n,?_⟩,?_⟩
  · apply Prod.ext <;> simp [upperRight,lowerLeft]
  · dsimp [upperRight,lowerLeft]
    linarith [show (0 : ℝ) ≤ n by positivity]

theorem lowerLeft_mem_bottom (n : ℕ) : lowerLeft n ∈ bottomPolyhexArc n :=
  ⟨upperRight n,upperRight_mem_top n,by simp [upperRight]⟩

theorem lowerRight_mem_bottom (n : ℕ) : lowerRight n ∈ bottomPolyhexArc n :=
  ⟨upperLeft n,upperLeft_mem_top n,rfl⟩

theorem topPolyhexArc_width_image (n : ℕ) :
    Prod.fst '' topPolyhexArc n = Icc (-(n : ℝ)-1/3) ((n : ℝ)+1/3) := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨hp.2,?_⟩
    have h : p.1 ∈ Prod.fst '' topPolyhexRawArc n := ⟨p,hp.1,rfl⟩
    rw [topPolyhexRawArc_width_image] at h
    exact h.2
  · intro hx
    have hx' : x ∈ Prod.fst '' topPolyhexRawArc n := by
      rw [topPolyhexRawArc_width_image]
      exact ⟨by linarith [hx.1],hx.2⟩
    obtain ⟨p,hp,hpx⟩ := hx'
    exact ⟨p,⟨hp,by change -(n : ℝ)-1/3 ≤ p.1; rw [hpx]; exact hx.1⟩,hpx⟩

theorem topPolyhexArc_fst_injective (n : ℕ) : Set.InjOn Prod.fst (topPolyhexArc n) :=
  (topPolyhexRawArc_fst_injective n).mono inter_subset_left

theorem bottomPolyhexArc_fst_injective (n : ℕ) : Set.InjOn Prod.fst (bottomPolyhexArc n) :=
  (bottomPolyhexRawArc_fst_injective n).mono (bottomPolyhexArc_subset_raw n)

theorem left_right_arcs_disjoint (n : ℕ) : Disjoint (leftPolyhexArc n) (rightPolyhexArc n) := by
  rw [Set.disjoint_left]
  intro p hl hr
  have h1 := leftArc_x_bound hl
  have h2 := rightArc_x_bound hr
  linarith [show (0 : ℝ) ≤ n by positivity]

theorem top_bottom_arcs_disjoint (n : ℕ) : Disjoint (topPolyhexArc n) (bottomPolyhexArc n) := by
  rw [Set.disjoint_left]
  intro p ht hb
  have h1 := topArc_y_bound ht
  have h2 := bottomArc_y_bound hb
  linarith [show (0 : ℝ) ≤ n by positivity]

theorem left_top_intersection (n : ℕ) :
    leftPolyhexArc n ∩ topPolyhexArc n = {upperLeft n} := by
  apply subset_antisymm
  · intro p hp
    have h1 := leftArc_x_bound hp.1
    have h2 := hp.2.2
    apply Set.mem_singleton_iff.mpr
    apply topPolyhexArc_fst_injective n hp.2 (upperLeft_mem_top n)
    change p.1 = -(n : ℝ)-1/3
    exact le_antisymm h1 h2
  · intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨upperLeft_mem n,upperLeft_mem_top n⟩

theorem right_top_intersection (n : ℕ) :
    rightPolyhexArc n ∩ topPolyhexArc n = {upperRight n} := by
  apply subset_antisymm
  · intro p hp
    have h1 := rightArc_x_bound hp.1
    have h2 : p.1 ∈ Icc (-(n : ℝ)-1/3) ((n : ℝ)+1/3) := by
      rw [← topPolyhexArc_width_image]
      exact ⟨p,hp.2,rfl⟩
    apply Set.mem_singleton_iff.mpr
    apply topPolyhexArc_fst_injective n hp.2 (upperRight_mem_top n)
    dsimp [upperRight,lowerLeft]
    linarith [h2.2]
  · intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨upperRight_mem n,upperRight_mem_top n⟩

theorem left_bottom_intersection (n : ℕ) :
    leftPolyhexArc n ∩ bottomPolyhexArc n = {lowerLeft n} := by
  apply subset_antisymm
  · rintro p ⟨hp,q,hq,rfl⟩
    have hright : q ∈ rightPolyhexArc n := by
      simpa only [neg_neg] using (neg_mem_rightPolyhexArc_iff n (-q)).mpr hp
    have hqeq : q = upperRight n := by
      apply Set.mem_singleton_iff.mp
      rw [← right_top_intersection]
      exact ⟨hright,hq⟩
    rw [hqeq]
    simpa only [upperRight,neg_neg] using Set.mem_singleton (lowerLeft n)
  · intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨lowerLeft_mem n,lowerLeft_mem_bottom n⟩

theorem right_bottom_intersection (n : ℕ) :
    rightPolyhexArc n ∩ bottomPolyhexArc n = {lowerRight n} := by
  apply subset_antisymm
  · rintro p ⟨hp,q,hq,rfl⟩
    have hleft := (neg_mem_rightPolyhexArc_iff n q).mp hp
    have hqeq : q = upperLeft n := by
      apply Set.mem_singleton_iff.mp
      rw [← left_top_intersection]
      exact ⟨hleft,hq⟩
    rw [hqeq]
    exact Set.mem_singleton _
  · intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨lowerRight_mem n,lowerRight_mem_bottom n⟩

theorem bottomPolyhexArc_width_image (n : ℕ) :
    Prod.fst '' bottomPolyhexArc n = Icc (-(n : ℝ)-1/3) ((n : ℝ)+1/3) := by
  ext x
  constructor
  · rintro ⟨p,⟨q,hq,rfl⟩,rfl⟩
    have h : q.1 ∈ Prod.fst '' topPolyhexArc n := ⟨q,hq,rfl⟩
    rw [topPolyhexArc_width_image] at h
    change -(n : ℝ)-1/3 ≤ -q.1 ∧ -q.1 ≤ (n : ℝ)+1/3
    constructor <;> linarith [h.1,h.2]
  · intro hx
    have hx' : -x ∈ Prod.fst '' topPolyhexArc n := by
      rw [topPolyhexArc_width_image]
      constructor <;> linarith [hx.1,hx.2]
    obtain ⟨p,hp,hpx⟩ := hx'
    exact ⟨-p,⟨p,hp,rfl⟩,by change -p.1 = x; linarith⟩

/-- A continuous injective coordinate on a compact side with an exact
interval image gives its genuine interval homeomorphism. -/
noncomputable def compactCoordinateHomeomorph (s : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ)
    (hs : IsCompact s) (hf : Continuous f) (hi : Set.InjOn f s)
    (a b : ℝ) (hrange : f '' s = Icc a b) : s ≃ₜ Icc a b := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let g : s → Icc a b := fun p => ⟨f p.val,by rw [← hrange]; exact ⟨p.val,p.property,rfl⟩⟩
  have hc : Continuous g := (hf.comp continuous_subtype_val).subtype_mk _
  have hb : Function.Bijective g := by
    constructor
    · intro p q h
      apply Subtype.ext
      exact hi p.property q.property (congrArg Subtype.val h)
    · intro y
      have hy : y.val ∈ f '' s := by simpa only [hrange] using y.property
      obtain ⟨p,hp,heq⟩ := hy
      exact ⟨⟨p,hp⟩,Subtype.ext heq⟩
  exact IsHomeomorph.homeomorph g (isHomeomorph_iff_continuous_bijective.mpr ⟨hc,hb⟩)

noncomputable def rightPolyhexArcHomeomorph (n : ℕ) :
    ↥(rightPolyhexArc n) ≃ₜ ↥(Icc (-(n : ℝ)-2/3) ((n : ℝ)+1/3)) :=
  compactCoordinateHomeomorph _ Prod.snd (rightPolyhexArc_isCompact n) continuous_snd
    (rightPolyhexArc_snd_injective n) _ _ (rightPolyhexArc_height_image n)

noncomputable def topPolyhexArcHomeomorph (n : ℕ) :
    ↥(topPolyhexArc n) ≃ₜ ↥(Icc (-(n : ℝ)-1/3) ((n : ℝ)+1/3)) :=
  compactCoordinateHomeomorph _ Prod.fst (topPolyhexArc_isCompact n) continuous_fst
    (topPolyhexArc_fst_injective n) _ _ (topPolyhexArc_width_image n)

noncomputable def bottomPolyhexArcHomeomorph (n : ℕ) :
    ↥(bottomPolyhexArc n) ≃ₜ ↥(Icc (-(n : ℝ)-1/3) ((n : ℝ)+1/3)) :=
  compactCoordinateHomeomorph _ Prod.fst (bottomPolyhexArc_isCompact n) continuous_fst
    (bottomPolyhexArc_fst_injective n) _ _ (bottomPolyhexArc_width_image n)

#print axioms frontier_touches_outside_cell
#print axioms polyhex_frontier_subset_rawArcs
#print axioms topPolyhexArc_preconnected
#print axioms polyhex_frontier_eq_arcs
#print axioms topPolyhexArcHomeomorph
#print axioms right_bottom_intersection

end ExceptionalTimes.PairSquareSewing
