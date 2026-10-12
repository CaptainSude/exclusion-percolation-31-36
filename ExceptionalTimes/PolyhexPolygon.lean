import ExceptionalTimes.PolyhexBoundary
import Mathlib.Analysis.Convex.Topology

open Set

namespace ExceptionalTimes.PairSquareSewing

noncomputable def westLower (u : Site) : ℝ × ℝ := ((u.1 : ℝ)-1/3,(u.2 : ℝ)-1/3)
noncomputable def westTip (u : Site) : ℝ × ℝ := ((u.1 : ℝ)-2/3,(u.2 : ℝ)+1/3)
noncomputable def westUpper (u : Site) : ℝ × ℝ := ((u.1 : ℝ)-1/3,(u.2 : ℝ)+2/3)

theorem westLower_mem_cell (u : Site) : westLower u ∈ HexCells.cell u := by
  dsimp [westLower,HexCells.cell]
  repeat' constructor
  all_goals linarith

theorem westTip_mem_cell (u : Site) : westTip u ∈ HexCells.cell u := by
  dsimp [westTip,HexCells.cell]
  repeat' constructor
  all_goals linarith

theorem westUpper_mem_cell (u : Site) : westUpper u ∈ HexCells.cell u := by
  dsimp [westUpper,HexCells.cell]
  repeat' constructor
  all_goals linarith

theorem leftFacets_eq_segments (u : Site) : leftFacets u =
    segment ℝ (westLower u) (westTip u) ∪ segment ℝ (westTip u) (westUpper u) := by
  apply subset_antisymm
  · intro p hp
    rcases hp with ⟨⟨⟨ha,ha'⟩,⟨hb,hb'⟩,⟨hc,hc'⟩⟩,h | h⟩
    · apply Or.inl
      rw [segment_eq_image']
      let t : ℝ := (3*(p.2-(u.2 : ℝ))+1)/2
      refine ⟨t,⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩,?_⟩
      apply Prod.ext
      · change (u.1 : ℝ)-1/3+t*((u.1 : ℝ)-2/3-((u.1 : ℝ)-1/3)) = p.1
        dsimp [t]
        nlinarith
      · change (u.2 : ℝ)-1/3+t*((u.2 : ℝ)+1/3-((u.2 : ℝ)-1/3)) = p.2
        dsimp [t]
        ring
    · apply Or.inr
      rw [segment_eq_image']
      let t : ℝ := 3*(p.2-(u.2 : ℝ))-1
      refine ⟨t,⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩,?_⟩
      apply Prod.ext
      · change (u.1 : ℝ)-2/3+t*((u.1 : ℝ)-1/3-((u.1 : ℝ)-2/3)) = p.1
        dsimp [t]
        nlinarith
      · change (u.2 : ℝ)+1/3+t*((u.2 : ℝ)+2/3-((u.2 : ℝ)+1/3)) = p.2
        dsimp [t]
        ring
  · intro p hp
    rcases hp with hp | hp
    · refine ⟨(HexCells.convex_cell u).segment_subset (westLower_mem_cell u) (westTip_mem_cell u) hp,Or.inl ?_⟩
      have hconv : Convex ℝ {p : ℝ × ℝ | 2*p.1+p.2 = 2*u.1+u.2-1} := by
        simpa only [one_mul] using convex_hyperplane (linear_axial 2 1) (2*u.1+u.2-1)
      exact hconv.segment_subset (by dsimp [westLower]; ring) (by dsimp [westTip]; ring) hp
    · refine ⟨(HexCells.convex_cell u).segment_subset (westTip_mem_cell u) (westUpper_mem_cell u) hp,Or.inr ?_⟩
      have hconv : Convex ℝ {p : ℝ × ℝ | p.1-p.2 = u.1-u.2-1} := by
        simpa only [one_mul,neg_one_mul,sub_eq_add_neg] using convex_hyperplane (linear_axial 1 (-1)) (u.1-u.2-1)
      exact hconv.segment_subset (by dsimp [westTip]; ring) (by dsimp [westUpper]; ring) hp

/-- A finite union of genuine closed straight segments. -/
def FiniteSegments (s : Set (ℝ × ℝ)) : Prop :=
  ∃ E : Finset ((ℝ × ℝ) × (ℝ × ℝ)), s = ⋃ e ∈ E, segment ℝ e.1 e.2

theorem finiteSegments_empty : FiniteSegments ∅ := by
  refine ⟨∅,?_⟩
  simp

theorem FiniteSegments.union {s t : Set (ℝ × ℝ)} (hs : FiniteSegments s)
    (ht : FiniteSegments t) : FiniteSegments (s ∪ t) := by
  classical
  obtain ⟨E,rfl⟩ := hs
  obtain ⟨F,rfl⟩ := ht
  refine ⟨E∪F,?_⟩
  ext p
  simp only [mem_union,mem_iUnion,Finset.mem_union]
  aesop

theorem FiniteSegments.biUnion {ι : Type*} (S : Finset ι) (f : ι → Set (ℝ × ℝ))
    (hf : ∀ i ∈ S, FiniteSegments (f i)) : FiniteSegments (⋃ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using finiteSegments_empty
  | @insert i S hi ih =>
    have heq : (⋃ j ∈ insert i S, f j) = f i ∪ ⋃ j ∈ S, f j := by ext p; simp
    rw [heq]
    exact (hf i (Finset.mem_insert_self _ _)).union (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem FiniteSegments.affine_image {s : Set (ℝ × ℝ)} (hs : FiniteSegments s)
    (f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ)) : FiniteSegments (f '' s) := by
  classical
  obtain ⟨E,rfl⟩ := hs
  refine ⟨E.image (fun e => (f e.1,f e.2)),?_⟩
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨e,he,hqe⟩ := mem_iUnion₂.mp hq
    refine mem_iUnion₂_of_mem (Finset.mem_image.mpr ⟨e,he,rfl⟩) ?_
    change f q ∈ segment ℝ (f e.1) (f e.2)
    rw [← image_segment]
    exact ⟨q,hqe,rfl⟩
  · intro hp
    obtain ⟨e,he,hpe⟩ := mem_iUnion₂.mp hp
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
    change p ∈ segment ℝ (f d.1) (f d.2) at hpe
    rw [← image_segment] at hpe
    obtain ⟨q,hq,rfl⟩ := hpe
    exact ⟨q,mem_iUnion₂_of_mem hd hq,rfl⟩

theorem leftFacets_finiteSegments (u : Site) : FiniteSegments (leftFacets u) := by
  classical
  refine ⟨{(westLower u,westTip u),(westTip u,westUpper u)},?_⟩
  simp only [leftFacets_eq_segments,Finset.mem_insert,Finset.mem_singleton,iUnion_iUnion_eq_or_left,
    iUnion_iUnion_eq_left]

theorem leftPolyhexArc_finiteSegments (n : ℕ) : FiniteSegments (leftPolyhexArc n) :=
  FiniteSegments.biUnion _ _ (fun u _ => leftFacets_finiteSegments u)

theorem rightPolyhexArc_finiteSegments (n : ℕ) : FiniteSegments (rightPolyhexArc n) := by
  rw [rightPolyhexArc_eq_neg]
  exact (leftPolyhexArc_finiteSegments n).affine_image (-LinearMap.id).toAffineMap

theorem topPolyhexRawArc_finiteSegments (n : ℕ) : FiniteSegments (topPolyhexRawArc n) :=
  (rightPolyhexArc_finiteSegments n).affine_image (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap.toAffineMap

theorem bottomPolyhexRawArc_finiteSegments (n : ℕ) : FiniteSegments (bottomPolyhexRawArc n) :=
  (leftPolyhexArc_finiteSegments n).affine_image (LinearEquiv.prodComm ℝ ℝ ℝ).toLinearMap.toAffineMap

theorem polyhex_frontier_finiteSegments (n : ℕ) : FiniteSegments (frontier (polyhex n)) := by
  rw [polyhex_frontier_eq_rawArcs]
  exact (((leftPolyhexArc_finiteSegments n).union (rightPolyhexArc_finiteSegments n)).union
    (topPolyhexRawArc_finiteSegments n)).union (bottomPolyhexRawArc_finiteSegments n)

theorem hexCenter_mem_interior (u : Site) : HexCells.center u ∈ interior (HexCells.cell u) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (HexCells.center u) (by norm_num : (0 : ℝ)<1/4))
  intro p hp
  have hd : max |p.1-(u.1 : ℝ)| |p.2-(u.2 : ℝ)| < 1/4 := hp
  have h1 := abs_lt.mp ((le_max_left _ _).trans_lt hd)
  have h2 := abs_lt.mp ((le_max_right _ _).trans_lt hd)
  dsimp [HexCells.cell]
  repeat' constructor
  all_goals linarith [h1.1,h1.2,h2.1,h2.2]

theorem hexCell_closure_interior (u : Site) : closure (interior (HexCells.cell u)) = HexCells.cell u := by
  rw [(HexCells.convex_cell u).closure_interior_eq_closure_of_nonempty_interior
    ⟨HexCells.center u,hexCenter_mem_interior u⟩, (HexCells.isClosed_cell u).closure_eq]

theorem polyhex_closure_interior (n : ℕ) : closure (interior (polyhex n)) = polyhex n := by
  apply subset_antisymm
  · exact closure_minimal interior_subset (polyhex_isCompact n).isClosed
  · intro p hp
    obtain ⟨u,hu,hpu⟩ := mem_iUnion₂.mp hp
    have hsub : HexCells.cell u ⊆ polyhex n := fun _ h => mem_iUnion₂_of_mem hu h
    apply closure_mono (interior_mono hsub)
    rwa [hexCell_closure_interior]

/-- A compact simple arc certified by a continuous one-to-one real
coordinate and its exact nondegenerate interval image. -/
def CoordinateArc (s : Set (ℝ × ℝ)) (a b : ℝ × ℝ) : Prop :=
  IsCompact s ∧ a ∈ s ∧ b ∈ s ∧ ∃ f : (ℝ × ℝ) → ℝ,
    Continuous f ∧ Set.InjOn f s ∧ f a < f b ∧ f '' s = Icc (f a) (f b)

/-- Literal geometric presentation of a bounded polygon quad. Its
carrier is regular closed, and its frontier consists of four simple
arcs meeting exactly at the marked corners, covered by finitely many
straight segments. These are geometric facts, not crossing assumptions. -/
structure PolygonQuad where
  carrier : Set (ℝ × ℝ)
  left : Set (ℝ × ℝ)
  right : Set (ℝ × ℝ)
  top : Set (ℝ × ℝ)
  bottom : Set (ℝ × ℝ)
  lowerLeft : ℝ × ℝ
  upperLeft : ℝ × ℝ
  upperRight : ℝ × ℝ
  lowerRight : ℝ × ℝ
  compact : IsCompact carrier
  regularClosed : closure (interior carrier) = carrier
  left_arc : CoordinateArc left lowerLeft upperLeft
  right_arc : CoordinateArc right lowerRight upperRight
  top_arc : CoordinateArc top upperLeft upperRight
  bottom_arc : CoordinateArc bottom lowerLeft lowerRight
  frontier_eq : frontier carrier = left ∪ right ∪ top ∪ bottom
  polygonal : FiniteSegments (frontier carrier)
  left_right : Disjoint left right
  top_bottom : Disjoint top bottom
  left_top : left ∩ top = {upperLeft}
  right_top : right ∩ top = {upperRight}
  left_bottom : left ∩ bottom = {lowerLeft}
  right_bottom : right ∩ bottom = {lowerRight}

noncomputable def axialBoxPolygonQuad (n : ℕ) : PolygonQuad where
  carrier := polyhex n
  left := leftPolyhexArc n
  right := rightPolyhexArc n
  top := topPolyhexArc n
  bottom := bottomPolyhexArc n
  lowerLeft := lowerLeft n
  upperLeft := upperLeft n
  upperRight := upperRight n
  lowerRight := lowerRight n
  compact := polyhex_isCompact n
  regularClosed := polyhex_closure_interior n
  left_arc := by
    refine ⟨leftPolyhexArc_isCompact n,lowerLeft_mem n,upperLeft_mem n,Prod.snd,
      continuous_snd,leftPolyhexArc_snd_injective n,?_,leftPolyhexArc_height_image n⟩
    dsimp [lowerLeft,upperLeft]
    linarith [show (0 : ℝ) ≤ n by positivity]
  right_arc := by
    refine ⟨rightPolyhexArc_isCompact n,lowerRight_mem n,upperRight_mem n,Prod.snd,
      continuous_snd,rightPolyhexArc_snd_injective n,?_,?_⟩
    · dsimp [lowerRight,upperRight,lowerLeft,upperLeft]
      linarith [show (0 : ℝ) ≤ n by positivity]
    · simpa [lowerRight,upperRight,lowerLeft,upperLeft,add_comm,sub_eq_add_neg] using rightPolyhexArc_height_image n
  top_arc := by
    refine ⟨topPolyhexArc_isCompact n,upperLeft_mem_top n,upperRight_mem_top n,Prod.fst,
      continuous_fst,topPolyhexArc_fst_injective n,?_,?_⟩
    · dsimp [upperLeft,upperRight,lowerLeft]
      linarith [show (0 : ℝ) ≤ n by positivity]
    · simpa [upperLeft,upperRight,lowerLeft,add_comm] using topPolyhexArc_width_image n
  bottom_arc := by
    refine ⟨bottomPolyhexArc_isCompact n,lowerLeft_mem_bottom n,lowerRight_mem_bottom n,Prod.fst,
      continuous_fst,bottomPolyhexArc_fst_injective n,?_,?_⟩
    · dsimp [lowerLeft,lowerRight,upperLeft]
      linarith [show (0 : ℝ) ≤ n by positivity]
    · simpa [lowerLeft,lowerRight,upperLeft,add_comm] using bottomPolyhexArc_width_image n
  frontier_eq := polyhex_frontier_eq_arcs n
  polygonal := polyhex_frontier_finiteSegments n
  left_right := left_right_arcs_disjoint n
  top_bottom := top_bottom_arcs_disjoint n
  left_top := left_top_intersection n
  right_top := right_top_intersection n
  left_bottom := left_bottom_intersection n
  right_bottom := right_bottom_intersection n

#print axioms leftFacets_eq_segments
#print axioms polyhex_frontier_finiteSegments
#print axioms axialBoxPolygonQuad

end ExceptionalTimes.PairSquareSewing
