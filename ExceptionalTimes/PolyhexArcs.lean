import ExceptionalTimes.PolyhexTerminals
import ExceptionalTimes.HexTiling
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Homeomorph.Lemmas

open Set

namespace ExceptionalTimes.PairSquareSewing

theorem linear_axial (a b : ℝ) :
    IsLinearMap ℝ (fun p : ℝ × ℝ => a * p.1 + b * p.2) := by
  constructor
  · intro p q
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · intro c p
    change a * (c * p.1) + b * (c * p.2) = c * (a * p.1 + b * p.2)
    ring

theorem leftFacets_isClosed (u : Site) : IsClosed (leftFacets u) := by
  exact (HexCells.isClosed_cell u).inter
    ((isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const))

theorem leftFacets_isCompact (u : Site) : IsCompact (leftFacets u) :=
  (HexCells.isCompact_cell u).of_isClosed_subset (leftFacets_isClosed u) (fun _ hp => hp.1)

theorem leftFacets_preconnected (u : Site) : IsPreconnected (leftFacets u) := by
  let W : Set (ℝ × ℝ) := HexCells.cell u ∩
    {p | 2 * p.1 + p.2 = 2 * u.1 + u.2 - 1}
  let N : Set (ℝ × ℝ) := HexCells.cell u ∩
    {p | p.1 - p.2 = u.1 - u.2 - 1}
  have hW : Convex ℝ W := by
    simpa only [W, one_mul] using (HexCells.convex_cell u).inter
      (convex_hyperplane (linear_axial 2 1) (2 * u.1 + u.2 - 1))
  have hN : Convex ℝ N := by
    simpa only [N, one_mul, neg_one_mul, sub_eq_add_neg] using (HexCells.convex_cell u).inter
      (convex_hyperplane (linear_axial 1 (-1)) (u.1 - u.2 - 1))
  have hx : ((u.1 : ℝ) - 2 / 3, (u.2 : ℝ) + 1 / 3) ∈ W ∩ N := by
    have hcell : ((u.1 : ℝ) - 2 / 3, (u.2 : ℝ) + 1 / 3) ∈ HexCells.cell u := by
      dsimp [HexCells.cell]
      repeat' constructor
      all_goals linarith
    exact ⟨⟨hcell, by dsimp; ring⟩, ⟨hcell, by dsimp; ring⟩⟩
  have heq : leftFacets u = W ∪ N := by ext p; simp only [leftFacets, W, N, mem_ofPred_eq, mem_inter_iff, mem_union]; tauto
  rw [heq]
  exact hW.isPreconnected.union' ⟨_, hx⟩ hN.isPreconnected

theorem leftFacets_adjacent (x j : ℤ) :
    (leftFacets (x,j) ∩ leftFacets (x,j+1)).Nonempty := by
  let p : ℝ × ℝ := ((x : ℝ) - 1 / 3, (j : ℝ) + 2 / 3)
  have h₁ : p ∈ HexCells.cell (x,j) := by
    dsimp [p, HexCells.cell]
    repeat' constructor
    all_goals linarith
  have h₂ : p ∈ HexCells.cell (x,j+1) := by
    dsimp [p, HexCells.cell]
    push_cast
    repeat' constructor
    all_goals linarith
  exact ⟨p, ⟨h₁, Or.inr (by dsimp [p]; ring)⟩,
    ⟨h₂, Or.inl (by dsimp [p]; push_cast; ring)⟩⟩

theorem leftPolyhexArc_eq_rows (n : ℕ) :
    leftPolyhexArc n = ⋃ j ∈ Icc (-(n : ℤ)) (n : ℤ), leftFacets (-(n : ℤ),j) := by
  ext p
  constructor
  · intro hp
    obtain ⟨u, hu, hpu⟩ := mem_iUnion₂.mp hp
    obtain ⟨huD, hux⟩ := Finset.mem_filter.mp hu
    change u ∈ latticeBox n at huD
    simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at huD
    refine mem_iUnion₂_of_mem huD.2 ?_
    have heq : (-(n : ℤ),u.2) = u := Prod.ext hux.symm rfl
    rwa [heq]
  · intro hp
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hp
    refine mem_iUnion₂_of_mem ?_ hpj
    change (-(n : ℤ),j) ∈ (latticeBox n).filter (fun v => v.1 = -(n : ℤ))
    simp only [Finset.mem_filter, latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨le_rfl, by omega⟩, hj⟩, trivial⟩

theorem leftPolyhexArc_preconnected (n : ℕ) : IsPreconnected (leftPolyhexArc n) := by
  rw [leftPolyhexArc_eq_rows]
  apply IsPreconnected.biUnion_of_chain (s := fun j : ℤ => leftFacets (-(n : ℤ),j))
    (t := Icc (-(n : ℤ)) (n : ℤ)) ordConnected_Icc
  · intro j _
    exact leftFacets_preconnected _
  · intro j _ _
    simpa using leftFacets_adjacent (-(n : ℤ)) j

theorem leftPolyhexArc_isCompact (n : ℕ) : IsCompact (leftPolyhexArc n) :=
  (axialBoxQuad n).firstSide.isCompact_biUnion (fun u _ => leftFacets_isCompact u)

/-- Literal polygon endpoints of the left terminal arc. -/
noncomputable def lowerLeft (n : ℕ) : ℝ × ℝ := (-(n : ℝ) - 1 / 3, -(n : ℝ) - 1 / 3)
noncomputable def upperLeft (n : ℕ) : ℝ × ℝ := (-(n : ℝ) - 1 / 3, (n : ℝ) + 2 / 3)

theorem lowerLeft_mem (n : ℕ) : lowerLeft n ∈ leftPolyhexArc n := by
  rw [leftPolyhexArc_eq_rows]
  refine mem_iUnion₂_of_mem (show -(n : ℤ) ∈ Icc (-(n : ℤ)) (n : ℤ) by constructor <;> omega) ?_
  refine ⟨?_, Or.inl ?_⟩
  · dsimp [HexCells.cell, lowerLeft]
    push_cast
    repeat' constructor
    all_goals linarith
  · dsimp [lowerLeft]
    push_cast
    ring

theorem upperLeft_mem (n : ℕ) : upperLeft n ∈ leftPolyhexArc n := by
  rw [leftPolyhexArc_eq_rows]
  refine mem_iUnion₂_of_mem (show (n : ℤ) ∈ Icc (-(n : ℤ)) (n : ℤ) by constructor <;> omega) ?_
  refine ⟨?_, Or.inr ?_⟩
  · dsimp [HexCells.cell, upperLeft]
    push_cast
    repeat' constructor
    all_goals linarith
  · dsimp [upperLeft]
    push_cast
    ring

theorem leftFacets_height {u : Site} {p : ℝ × ℝ} (hp : p ∈ leftFacets u) :
    (u.2 : ℝ) - 1/3 ≤ p.2 ∧ p.2 ≤ (u.2 : ℝ) + 2/3 := by
  have hx := leftFacets_coordinate hp
  rcases hp with ⟨⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩, h | h⟩
  all_goals constructor <;> linarith

/-- The entire side is a compact connected graph over precisely this
closed height interval, so it is an actual simple arc. -/
theorem leftPolyhexArc_height_image (n : ℕ) :
    Prod.snd '' leftPolyhexArc n = Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3) := by
  apply subset_antisymm
  · rintro y ⟨p, hp, rfl⟩
    rw [leftPolyhexArc_eq_rows] at hp
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hp
    have hb := leftFacets_height hpj
    have hj₁ : -(n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hj₂ : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj.2
    constructor <;> linarith
  · have hconn := (leftPolyhexArc_preconnected n).image Prod.snd continuous_snd.continuousOn
    apply hconn.Icc_subset
    · exact ⟨lowerLeft n, lowerLeft_mem n, rfl⟩
    · exact ⟨upperLeft n, upperLeft_mem n, rfl⟩

noncomputable def leftPolyhexArcHomeomorph (n : ℕ) :
    ↥(leftPolyhexArc n) ≃ₜ ↥(Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3)) := by
  letI : CompactSpace ↥(leftPolyhexArc n) := isCompact_iff_compactSpace.mp (leftPolyhexArc_isCompact n)
  let f : ↥(leftPolyhexArc n) → ↥(Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3)) :=
    fun p => ⟨p.val.2, by rw [← leftPolyhexArc_height_image]; exact ⟨p.val, p.property, rfl⟩⟩
  have hc : Continuous f := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hb : Function.Bijective f := by
    constructor
    · intro p q h
      apply Subtype.ext
      exact leftPolyhexArc_snd_injective n p.property q.property (congrArg Subtype.val h)
    · intro y
      have hy : y.val ∈ Prod.snd '' leftPolyhexArc n := by
        simpa only [leftPolyhexArc_height_image] using y.property
      obtain ⟨p, hp, heq⟩ := hy
      exact ⟨⟨p,hp⟩, Subtype.ext heq⟩
  exact IsHomeomorph.homeomorph f (isHomeomorph_iff_continuous_bijective.mpr ⟨hc,hb⟩)

theorem neg_mem_hexCell_iff (u : Site) (p : ℝ × ℝ) :
    -p ∈ HexCells.cell (-u) ↔ p ∈ HexCells.cell u := by
  simp only [HexCells.cell, mem_ofPred, mem_Icc, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  constructor <;> rintro ⟨⟨ha,ha'⟩,⟨hb,hb'⟩,⟨hc,hc'⟩⟩
  all_goals repeat' constructor
  all_goals linarith

theorem neg_mem_rightFacets_iff (u : Site) (p : ℝ × ℝ) :
    -p ∈ rightFacets (-u) ↔ p ∈ leftFacets u := by
  simp only [rightFacets, leftFacets, mem_ofPred, neg_mem_hexCell_iff,
    Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  constructor
  · rintro ⟨hc,h | h⟩
    · exact ⟨hc,Or.inl (by linarith)⟩
    · exact ⟨hc,Or.inr (by linarith)⟩
  · rintro ⟨hc,h | h⟩
    · exact ⟨hc,Or.inl (by linarith)⟩
    · exact ⟨hc,Or.inr (by linarith)⟩

theorem neg_mem_latticeBox_iff (n : ℕ) (u : Site) :
    -u ∈ latticeBox n ↔ u ∈ latticeBox n := by
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc,
    Prod.fst_neg, Prod.snd_neg]
  omega

theorem neg_mem_rightPolyhexArc_iff (n : ℕ) (p : ℝ × ℝ) :
    -p ∈ rightPolyhexArc n ↔ p ∈ leftPolyhexArc n := by
  constructor
  · intro hp
    obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
    refine mem_iUnion₂_of_mem (i := -u) ?_ ?_
    · obtain ⟨huD,huR⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(neg_mem_latticeBox_iff n u).mpr huD, by simpa using congrArg Neg.neg huR⟩
    · have h := (neg_mem_rightFacets_iff (-u) p).mp
      simpa only [neg_neg] using h (by simpa only [neg_neg] using hpu)
  · intro hp
    obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
    refine mem_iUnion₂_of_mem (i := -u) ?_ ((neg_mem_rightFacets_iff u p).mpr hpu)
    obtain ⟨huD,huL⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨(neg_mem_latticeBox_iff n u).mpr huD, by simpa using congrArg Neg.neg huL⟩

theorem rightPolyhexArc_eq_neg (n : ℕ) :
    rightPolyhexArc n = Neg.neg '' leftPolyhexArc n := by
  ext p
  constructor
  · intro hp
    exact ⟨-p, (neg_mem_rightPolyhexArc_iff n (-p)).mp (by simpa only [neg_neg] using hp), neg_neg p⟩
  · rintro ⟨q,hq,rfl⟩
    exact (neg_mem_rightPolyhexArc_iff n q).mpr hq

theorem rightPolyhexArc_preconnected (n : ℕ) : IsPreconnected (rightPolyhexArc n) := by
  rw [rightPolyhexArc_eq_neg]
  exact (leftPolyhexArc_preconnected n).image Neg.neg continuous_neg.continuousOn

theorem rightPolyhexArc_isCompact (n : ℕ) : IsCompact (rightPolyhexArc n) := by
  rw [rightPolyhexArc_eq_neg]
  exact (leftPolyhexArc_isCompact n).image continuous_neg

theorem rightPolyhexArc_height_image (n : ℕ) :
    Prod.snd '' rightPolyhexArc n = Icc (-(n : ℝ)-2/3) ((n : ℝ)+1/3) := by
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    have h : (-p).2 ∈ Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3) := by
      rw [← leftPolyhexArc_height_image]
      exact ⟨-p,(neg_mem_rightPolyhexArc_iff n (-p)).mp (by simpa only [neg_neg] using hp),rfl⟩
    change -(n : ℝ)-1/3 ≤ -p.2 ∧ -p.2 ≤ (n : ℝ)+2/3 at h
    constructor <;> linarith [h.1,h.2]
  · intro hy
    have h : -y ∈ Prod.snd '' leftPolyhexArc n := by
      rw [leftPolyhexArc_height_image]
      constructor <;> linarith [hy.1,hy.2]
    obtain ⟨p,hp,hpy⟩ := h
    exact ⟨-p,(neg_mem_rightPolyhexArc_iff n p).mpr hp,by change -p.2 = y; linarith⟩

theorem swap_mem_hexCell_iff (u : Site) (p : ℝ × ℝ) :
    p.swap ∈ HexCells.cell u.swap ↔ p ∈ HexCells.cell u := by
  simp only [HexCells.cell, mem_ofPred, mem_Icc, Prod.fst_swap, Prod.snd_swap]
  constructor <;> rintro ⟨⟨ha,ha'⟩,⟨hb,hb'⟩,⟨hc,hc'⟩⟩
  all_goals repeat' constructor
  all_goals linarith

theorem swap_mem_latticeBox_iff (n : ℕ) (u : Site) :
    u.swap ∈ latticeBox n ↔ u ∈ latticeBox n := by
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc,
    Prod.fst_swap, Prod.snd_swap, and_comm]

theorem swap_mem_polyhex_iff (n : ℕ) (p : ℝ × ℝ) : p.swap ∈ polyhex n ↔ p ∈ polyhex n := by
  constructor <;> intro hp
  · obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
    exact mem_iUnion₂_of_mem ((swap_mem_latticeBox_iff n u).mpr hu)
      ((swap_mem_hexCell_iff u.swap p).mp (by simpa only [Prod.swap_swap] using hpu))
  · obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
    exact mem_iUnion₂_of_mem ((swap_mem_latticeBox_iff n u).mpr hu)
      ((swap_mem_hexCell_iff u p).mpr hpu)

def topPolyhexRawArc (n : ℕ) : Set (ℝ × ℝ) := Prod.swap '' rightPolyhexArc n
def bottomPolyhexRawArc (n : ℕ) : Set (ℝ × ℝ) := Prod.swap '' leftPolyhexArc n

theorem topPolyhexRawArc_preconnected (n : ℕ) : IsPreconnected (topPolyhexRawArc n) :=
  (rightPolyhexArc_preconnected n).image Prod.swap continuous_swap.continuousOn

theorem bottomPolyhexRawArc_preconnected (n : ℕ) : IsPreconnected (bottomPolyhexRawArc n) :=
  (leftPolyhexArc_preconnected n).image Prod.swap continuous_swap.continuousOn

theorem topPolyhexRawArc_isCompact (n : ℕ) : IsCompact (topPolyhexRawArc n) :=
  (rightPolyhexArc_isCompact n).image continuous_swap

theorem bottomPolyhexRawArc_isCompact (n : ℕ) : IsCompact (bottomPolyhexRawArc n) :=
  (leftPolyhexArc_isCompact n).image continuous_swap

theorem topPolyhexRawArc_fst_injective (n : ℕ) : Set.InjOn Prod.fst (topPolyhexRawArc n) := by
  rintro p ⟨a,ha,rfl⟩ q ⟨b,hb,rfl⟩ h
  exact congrArg Prod.swap (rightPolyhexArc_snd_injective n ha hb h)

theorem bottomPolyhexRawArc_fst_injective (n : ℕ) : Set.InjOn Prod.fst (bottomPolyhexRawArc n) := by
  rintro p ⟨a,ha,rfl⟩ q ⟨b,hb,rfl⟩ h
  exact congrArg Prod.swap (leftPolyhexArc_snd_injective n ha hb h)

theorem topPolyhexRawArc_width_image (n : ℕ) :
    Prod.fst '' topPolyhexRawArc n = Icc (-(n : ℝ)-2/3) ((n : ℝ)+1/3) := by
  simpa only [topPolyhexRawArc, image_image, Function.comp_def, Prod.fst_swap] using rightPolyhexArc_height_image n

theorem bottomPolyhexRawArc_width_image (n : ℕ) :
    Prod.fst '' bottomPolyhexRawArc n = Icc (-(n : ℝ)-1/3) ((n : ℝ)+2/3) := by
  simpa only [bottomPolyhexRawArc, image_image, Function.comp_def, Prod.fst_swap] using leftPolyhexArc_height_image n

#print axioms leftPolyhexArcHomeomorph
#print axioms rightPolyhexArc_preconnected

end ExceptionalTimes.PairSquareSewing
