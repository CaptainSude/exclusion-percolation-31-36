import ExceptionalTimes.StraightBoxCells

open Set

namespace ExceptionalTimes.PairSquareSewing

private theorem vertical_eq_image (x lo hi : ℝ) :
    {p : ℝ×ℝ | p.1=x ∧ p.2∈Icc lo hi} = (fun t => (x,t)) '' Icc lo hi := by
  ext p
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨p.2,hy,Prod.ext hx.symm rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨rfl,ht⟩

private theorem horizontal_eq_image (y lo hi : ℝ) :
    {p : ℝ×ℝ | p.2=y ∧ p.1∈Icc lo hi} = (fun t => (t,y)) '' Icc lo hi := by
  ext p
  constructor
  · rintro ⟨hy,hx⟩
    exact ⟨p.1,hx,Prod.ext rfl hy.symm⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨rfl,ht⟩

private theorem vertical_coordinateArc (x lo hi : ℝ) (h : lo < hi) :
    CoordinateArc {p : ℝ×ℝ | p.1=x ∧ p.2∈Icc lo hi} (x,lo) (x,hi) := by
  refine ⟨?_,⟨rfl,⟨le_rfl,h.le⟩⟩,⟨rfl,⟨h.le,le_rfl⟩⟩,
    Prod.snd,continuous_snd,?_,h,?_⟩
  · rw [vertical_eq_image]
    exact isCompact_Icc.image (continuous_const.prodMk continuous_id)
  · intro p hp q hq he
    exact Prod.ext (hp.1.trans hq.1.symm) he
  · ext t
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp.2
    · intro ht
      exact ⟨(x,t),⟨rfl,ht⟩,rfl⟩

private theorem horizontal_coordinateArc (y lo hi : ℝ) (h : lo < hi) :
    CoordinateArc {p : ℝ×ℝ | p.2=y ∧ p.1∈Icc lo hi} (lo,y) (hi,y) := by
  refine ⟨?_,⟨rfl,⟨le_rfl,h.le⟩⟩,⟨rfl,⟨h.le,le_rfl⟩⟩,
    Prod.fst,continuous_fst,?_,h,?_⟩
  · rw [horizontal_eq_image]
    exact isCompact_Icc.image (continuous_id.prodMk continuous_const)
  · intro p hp q hq he
    exact Prod.ext he (hp.1.trans hq.1.symm)
  · ext t
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp.2
    · intro ht
      exact ⟨(t,y),⟨rfl,ht⟩,rfl⟩

private theorem segment_finiteSegments (a b : ℝ×ℝ) : FiniteSegments (segment ℝ a b) := by
  classical
  exact ⟨{(a,b)},by simp⟩

private theorem vertical_finiteSegments (x lo hi : ℝ) (h : lo ≤ hi) :
    FiniteSegments {p : ℝ×ℝ | p.1=x ∧ p.2∈Icc lo hi} := by
  let f : ℝ →ᵃ[ℝ] ℝ×ℝ := (AffineMap.const ℝ ℝ x).prod (AffineMap.id ℝ ℝ)
  have hf : (fun t => (x,t)) '' Icc lo hi = segment ℝ (x,lo) (x,hi) := by
    change f '' Icc lo hi = segment ℝ (f lo) (f hi)
    rw [← segment_eq_Icc h,image_segment]
  rw [vertical_eq_image,hf]
  exact segment_finiteSegments _ _

private theorem horizontal_finiteSegments (y lo hi : ℝ) (h : lo ≤ hi) :
    FiniteSegments {p : ℝ×ℝ | p.2=y ∧ p.1∈Icc lo hi} := by
  let f : ℝ →ᵃ[ℝ] ℝ×ℝ := (AffineMap.id ℝ ℝ).prod (AffineMap.const ℝ ℝ y)
  have hf : (fun t => (t,y)) '' Icc lo hi = segment ℝ (lo,y) (hi,y) := by
    change f '' Icc lo hi = segment ℝ (f lo) (f hi)
    rw [← segment_eq_Icc h,image_segment]
  rw [horizontal_eq_image,hf]
  exact segment_finiteSegments _ _

theorem axialRectangle_frontier (n : ℕ) :
    frontier (axialRectangle n) = straightLeft n ∪ straightRight n ∪ straightTop n ∪ straightBottom n := by
  have hn : -(n : ℝ) ≤ n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  change frontier ((Icc (-(n:ℝ)) n) ×ˢ (Icc (-(n:ℝ)) n)) = _
  rw [frontier_prod_eq,isClosed_Icc.closure_eq,frontier_Icc hn]
  ext p
  simp only [mem_union,mem_prod,mem_insert_iff,mem_singleton_iff,straightLeft,straightRight,
    straightTop,straightBottom,mem_ofPred]
  aesop

theorem axialRectangle_regularClosed (n : ℕ) (hn : 0 < n) :
    closure (interior (axialRectangle n)) = axialRectangle n := by
  have h : -(n : ℝ) < n := by exact_mod_cast (show -(n : ℤ) < n by omega)
  change closure (interior ((Icc (-(n:ℝ)) n) ×ˢ (Icc (-(n:ℝ)) n))) = _
  simp only [interior_prod_eq,interior_Icc,closure_prod_eq,closure_Ioo h.ne]
  rfl

/-- A genuine quad with exactly four straight macroscopic sides. Its
crossing dictionary is provided independently by StraightBoxCells. -/
noncomputable def straightBoxPolygonQuad (n : ℕ) (hn : 0 < n) : PolygonQuad where
  carrier := axialRectangle n
  left := straightLeft n
  right := straightRight n
  top := straightTop n
  bottom := straightBottom n
  lowerLeft := (-(n:ℝ),-(n:ℝ))
  upperLeft := (-(n:ℝ),(n:ℝ))
  upperRight := ((n:ℝ),(n:ℝ))
  lowerRight := ((n:ℝ),-(n:ℝ))
  compact := isCompact_Icc.prod isCompact_Icc
  regularClosed := axialRectangle_regularClosed n hn
  left_arc := vertical_coordinateArc _ _ _ (by exact_mod_cast (show -(n:ℤ)<n by omega))
  right_arc := vertical_coordinateArc _ _ _ (by exact_mod_cast (show -(n:ℤ)<n by omega))
  top_arc := horizontal_coordinateArc _ _ _ (by exact_mod_cast (show -(n:ℤ)<n by omega))
  bottom_arc := horizontal_coordinateArc _ _ _ (by exact_mod_cast (show -(n:ℤ)<n by omega))
  frontier_eq := axialRectangle_frontier n
  polygonal := by
    rw [axialRectangle_frontier]
    have hn' : -(n:ℝ) ≤ n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact (((vertical_finiteSegments _ _ _ hn').union (vertical_finiteSegments _ _ _ hn')).union
      (horizontal_finiteSegments _ _ _ hn')).union (horizontal_finiteSegments _ _ _ hn')
  left_right := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have h : -(n:ℝ) = n := hp.1.symm.trans hq.1
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    linarith
  top_bottom := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have h : (n:ℝ) = -n := hp.1.symm.trans hq.1
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    linarith
  left_top := by
    ext p
    simp only [straightLeft,straightTop,mem_inter_iff,mem_ofPred,mem_singleton_iff,Prod.ext_iff]
    have hn' : -(n:ℝ) ≤ n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    constructor
    · rintro ⟨⟨hx,_⟩,⟨hy,_⟩⟩
      exact ⟨hx,hy⟩
    · rintro ⟨hx,hy⟩
      exact ⟨⟨hx,by simp [hy,hn']⟩,⟨hy,by simp [hx,hn']⟩⟩
  right_top := by
    ext p
    simp only [straightRight,straightTop,mem_inter_iff,mem_ofPred,mem_singleton_iff,Prod.ext_iff]
    have hn' : -(n:ℝ) ≤ n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    constructor
    · rintro ⟨⟨hx,_⟩,⟨hy,_⟩⟩
      exact ⟨hx,hy⟩
    · rintro ⟨hx,hy⟩
      exact ⟨⟨hx,by simp [hy,hn']⟩,⟨hy,by simp [hx,hn']⟩⟩
  left_bottom := by
    ext p
    simp only [straightLeft,straightBottom,mem_inter_iff,mem_ofPred,mem_singleton_iff,Prod.ext_iff]
    have hn' : -(n:ℝ) ≤ n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    constructor
    · rintro ⟨⟨hx,_⟩,⟨hy,_⟩⟩
      exact ⟨hx,hy⟩
    · rintro ⟨hx,hy⟩
      exact ⟨⟨hx,by simp [hy,hn']⟩,⟨hy,by simp [hx,hn']⟩⟩
  right_bottom := by
    ext p
    simp only [straightRight,straightBottom,mem_inter_iff,mem_ofPred,mem_singleton_iff,Prod.ext_iff]
    have hn' : -(n:ℝ) ≤ n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    constructor
    · rintro ⟨⟨hx,_⟩,⟨hy,_⟩⟩
      exact ⟨hx,hy⟩
    · rintro ⟨hx,hy⟩
      exact ⟨⟨hx,by simp [hy,hn']⟩,⟨hy,by simp [hx,hn']⟩⟩

theorem straightBoxPolygonQuad_crossing_iff (n : ℕ) (hn : 0 < n) (ω : Configuration) :
    (straightBoxPolygonQuad n hn).Crossing ω ↔ (axialBoxQuad n).Crossing ω :=
  straightBox_crossing_iff_graph n ω

theorem straightBoxPolygonQuad_physicalCrossing_iff
    (n : ℕ) (hn : 0 < n) (P : Probe) (ω : Configuration) :
    (straightBoxPolygonQuad n hn).PhysicalCrossing P ω ↔ (axialBoxQuad n).Crossing ω :=
  ((straightBoxPolygonQuad n hn).physicalCrossing_iff P ω).trans
    (straightBoxPolygonQuad_crossing_iff n hn ω)

/-- An explicit bulk margin for the straight four-sided quad. -/
theorem closedBall_subset_physical_axialRectangle
    (P : Probe) (n : ℕ) (z : ℂ) (R : ℝ)
    (hmargin : 2*(‖z‖+R) < P.mesh*n) :
    Metric.closedBall z R ⊆ physicalHomeomorph P '' interior (axialRectangle n) := by
  intro w hw
  let p := (physicalHomeomorph P).symm w
  have hwp : (P.mesh : ℂ)*HexTiling.planeMap p = w :=
    (physicalHomeomorph P).apply_symm_apply w
  have hnorm : P.mesh*‖HexTiling.planeMap p‖ = ‖w‖ := by
    rw [← hwp,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.mesh_pos]
  have hwbound : ‖w‖ ≤ ‖z‖+R := by
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    have hdist : ‖w-z‖ ≤ R := by simpa [dist_eq_norm] using hw
    linarith
  obtain ⟨hx,hy⟩ := planeMap_coordinate_le_norm p
  have hnx : |p.1| < (n : ℝ) := by nlinarith [P.mesh_pos]
  have hny : |p.2| < (n : ℝ) := by nlinarith [P.mesh_pos]
  refine ⟨p,?_,hwp⟩
  change p ∈ interior ((Icc (-(n:ℝ)) n) ×ˢ (Icc (-(n:ℝ)) n))
  rw [interior_prod_eq,interior_Icc]
  exact ⟨abs_lt.mp hnx,abs_lt.mp hny⟩

/-- Published bulk necessity applies directly to the actual graph board;
there is no exterior-color completion in this dictionary. -/
theorem straightBox_localChangeArms_of_published
    (hsource : PublishedPolygonBulkArms) (n : ℕ) (hn : 0 < n) (P : Probe)
    (he : 16*P.mesh < P.innerRadius)
    (hbulk : Metric.closedBall (position P.mesh P.center) (2*P.outerRadius) ⊆
      physicalHomeomorph P '' interior (axialRectangle n)) :
    LocalChangeArms (axialBoxQuad n) P := by
  intro ω a b hab ha hb hchange
  apply hsource (straightBoxPolygonQuad n hn) P ω a b he hbulk
  · intro v hv
    exact changed_cell_in_buffered_ball P he hab hv
  · intro v hv
    have hreg := cell_meets_agreementShell_in_region P he hv
    exact ⟨ha hreg,hb hreg⟩
  · rw [straightBoxPolygonQuad_physicalCrossing_iff,
      straightBoxPolygonQuad_physicalCrossing_iff]
    intro h
    apply hchange
    exact decide_eq_decide.mpr h

theorem straightBox_localChangeArms
    (hsource : PublishedPolygonBulkArms) (n : ℕ) (hn : 0 < n) (P : Probe)
    (he : 16*P.mesh < P.innerRadius)
    (hmargin : 2*(‖position P.mesh P.center‖+2*P.outerRadius) < P.mesh*n) :
    LocalChangeArms (axialBoxQuad n) P :=
  straightBox_localChangeArms_of_published hsource n hn P he
    (closedBall_subset_physical_axialRectangle P n _ _ hmargin)

#print axioms straightBoxPolygonQuad
#print axioms straightBox_localChangeArms

end ExceptionalTimes.PairSquareSewing

