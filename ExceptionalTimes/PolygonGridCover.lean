import ExceptionalTimes.FiniteClosedPaths
import ExceptionalTimes.PolygonBoundarySide

/-! Integer-level axial polygons are finite unions of actual closed unit
rectangles. This is derived from the frontier and regular closedness, not
assumed as extra crossing geometry. It identifies the paper's connected
closed crossings with the path crossings used by the finite forest bound. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

def gridRectangle (z : Site) : Set (ℝ × ℝ) :=
  Icc (z.1:ℝ) (z.1+1) ×ˢ Icc (z.2:ℝ) (z.2+1)

def gridOpenRectangle (z : Site) : Set (ℝ × ℝ) :=
  Ioo (z.1:ℝ) (z.1+1) ×ˢ Ioo (z.2:ℝ) (z.2+1)

theorem gridOpenRectangle_closure (z : Site) :
    closure (gridOpenRectangle z) = gridRectangle z := by
  simp only [gridOpenRectangle,gridRectangle,closure_prod_eq,
    closure_Ioo (by linarith : (z.1:ℝ) ≠ z.1+1),
    closure_Ioo (by linarith : (z.2:ℝ) ≠ z.2+1)]

theorem not_integer_between {x : ℝ} (z : ℤ) (hlo : (z:ℝ)<x) (hhi : x<z+1) :
    x ∉ range (Int.cast : ℤ → ℝ) := by
  rintro ⟨k,rfl⟩
  have hzk : z<k := by exact_mod_cast hlo
  have hkz : k<z+1 := by exact_mod_cast hhi
  omega

theorem dense_noninteger : Dense (range (Int.cast : ℤ → ℝ))ᶜ := by
  apply Metric.dense_iff.mpr
  intro x r hr
  by_cases hx : x ∈ range (Int.cast : ℤ → ℝ)
  · obtain ⟨z,rfl⟩ := hx
    let d := min (r/2) (1/2)
    have hd : 0<d := lt_min (by linarith) (by norm_num)
    have hdr : d<r := (min_le_left _ _).trans_lt (by linarith)
    have hd1 : d<1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨(z:ℝ)+d,?_,not_integer_between z (by linarith) (by linarith)⟩
    simpa only [Metric.mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos hd] using hdr
  · exact ⟨x,by simpa only [Metric.mem_ball,dist_self] using hr,hx⟩

theorem gridRectangle_subset_of_contact {A : Set (ℝ × ℝ)} (hA : IsClosed A)
    (hfront : ∀ p ∈ frontier A,
      p.1 ∈ range (Int.cast : ℤ → ℝ) ∨ p.2 ∈ range (Int.cast : ℤ → ℝ))
    (z : Site) {p : ℝ × ℝ} (hp : p ∈ gridOpenRectangle z) (hpA : p ∈ A) :
    gridRectangle z ⊆ A := by
  have hconv : Convex ℝ (gridOpenRectangle z) :=
    (convex_Ioo (z.1:ℝ) (z.1+1)).prod (convex_Ioo (z.2:ℝ) (z.2+1))
  have havoid : ∀ q ∈ gridOpenRectangle z, q ∉ frontier A := by
    intro q hq hqf
    rcases hfront q hqf with hx | hy
    · exact not_integer_between z.1 hq.1.1 hq.1.2 hx
    · exact not_integer_between z.2 hq.2.1 hq.2.2 hy
  rcases preconnected_avoiding_frontier hA hconv.isPreconnected havoid with hi | ho
  · rw [← gridOpenRectangle_closure]
    exact closure_minimal (hi.trans interior_subset) hA
  · exact False.elim (ho hp hpA)

theorem finite_gridRectangle_cover {A : Set (ℝ × ℝ)} (hcompact : IsCompact A)
    (hregular : closure (interior A)=A)
    (hfront : ∀ p ∈ frontier A,
      p.1 ∈ range (Int.cast : ℤ → ℝ) ∨ p.2 ∈ range (Int.cast : ℤ → ℝ)) :
    ∃ s : Finset Site, A=⋃ z ∈ s, gridRectangle z := by
  classical
  obtain ⟨n,hn⟩ := compact_cellSupport_subset_box hcompact
  let s := (latticeBox n).filter (fun z => gridRectangle z ⊆ A)
  let U := ⋃ z ∈ s, gridRectangle z
  have hUclosed : IsClosed U := isClosed_biUnion_finset
    (fun _ _ => isClosed_Icc.prod isClosed_Icc)
  have hsub : U ⊆ A := by
    intro p hp
    obtain ⟨z,hz,hpz⟩ := mem_iUnion₂.mp hp
    exact (Finset.mem_filter.mp hz).2 hpz
  let N : Set (ℝ × ℝ) := (range (Int.cast : ℤ → ℝ))ᶜ ×ˢ (range (Int.cast : ℤ → ℝ))ᶜ
  have hN : Dense N := dense_noninteger.prod dense_noninteger
  have hgood : N ∩ interior A ⊆ U := by
    rintro p ⟨hpN,hpA⟩
    let z : Site := (⌊p.1⌋,⌊p.2⌋)
    have hpz : p ∈ gridOpenRectangle z :=
      ⟨⟨Int.floor_lt_self_iff.mpr hpN.1,Int.lt_floor_add_one p.1⟩,
       ⟨Int.floor_lt_self_iff.mpr hpN.2,Int.lt_floor_add_one p.2⟩⟩
    have hzA := gridRectangle_subset_of_contact hcompact.isClosed hfront z hpz (interior_subset hpA)
    have hzc : HexCells.center z ∈ A := hzA (by
      dsimp [HexCells.center,gridRectangle]
      exact ⟨⟨le_rfl,by linarith⟩,⟨le_rfl,by linarith⟩⟩)
    have hzbox := hn (show z ∈ cellSupport A from ⟨HexCells.center z,HexCells.center_mem_cell z,hzc⟩)
    exact mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hzbox,hzA⟩)
      ⟨⟨hpz.1.1.le,hpz.1.2.le⟩,⟨hpz.2.1.le,hpz.2.2.le⟩⟩
  have hi : interior A ⊆ U := by
    intro p hp
    have hc : p ∈ closure (N ∩ interior A) := isOpen_interior.closure_inter ⟨hN p,hp⟩
    exact closure_minimal hgood hUclosed hc
  refine ⟨s,subset_antisymm ?_ hsub⟩
  rw [← hregular]
  exact closure_minimal hi hUclosed

theorem AxialPolygonPresentation.finite_grid_cover {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E)
    (hinteger : ∀ i, ∃ level : ℤ, (A.edge i).level=(level:ℝ)) :
    ∃ s : Finset Site, Q.carrier=⋃ z ∈ s, gridRectangle z := by
  apply finite_gridRectangle_cover Q.compact Q.regularClosed
  intro p hp
  obtain ⟨i,hi⟩ := (A.frontier_iff p).mp hp
  obtain ⟨level,hlevel⟩ := hinteger i
  obtain ⟨t,_ht,rfl⟩ := hi
  have hline := (A.edge i).point_onLine t
  cases hh : (A.edge i).horizontal
  · left
    simp only [AxialSegment.onLine,hh,Bool.false_eq_true,ite_false] at hline
    simp only [AxialSegment.level,hh,Bool.false_eq_true,ite_false] at hlevel
    exact ⟨level,hlevel.symm.trans hline.symm⟩
  · right
    simp only [AxialSegment.onLine,hh,ite_true] at hline
    simp only [AxialSegment.level,hh,ite_true] at hlevel
    exact ⟨level,hlevel.symm.trans hline.symm⟩

theorem AxialPolygonPresentation.connectedCrossing_iff {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E)
    (hinteger : ∀ i, ∃ level : ℤ, (A.edge i).level=(level:ℝ)) (ω : Configuration) :
    Q.ConnectedCrossing ω ↔ Q.Crossing ω := by
  obtain ⟨s,hs⟩ := A.finite_grid_cover hinteger
  apply Q.connectedCrossing_iff_of_convex_cover (fun z : s => gridRectangle z.val)
  · intro z
    exact isClosed_Icc.prod isClosed_Icc
  · intro z
    exact (convex_Icc (z.val.1:ℝ) (z.val.1+1)).prod (convex_Icc (z.val.2:ℝ) (z.val.2+1))
  · rw [hs]
    ext p
    simp only [mem_iUnion]
    constructor
    · rintro ⟨z,hz,hp⟩
      exact ⟨⟨z,hz⟩,hp⟩
    · rintro ⟨⟨z,hz⟩,hp⟩
      exact ⟨z,hz,hp⟩

#print axioms finite_gridRectangle_cover
#print axioms AxialPolygonPresentation.connectedCrossing_iff

end ExceptionalTimes.PairSquareSewing
