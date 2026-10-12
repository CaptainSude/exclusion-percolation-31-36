import ExceptionalTimes.StraightBoxDefs

/-! Exact closed-cell crossing dictionary for the straight rectangle through
the outer board centers. Clipping retains every board adjacency and introduces
no exterior cells or artificial colors. -/

open Set

namespace ExceptionalTimes.PairSquareSewing

theorem axialRectangle_convex (n : ℕ) : Convex ℝ (axialRectangle n) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

theorem axialRectangle_closed (n : ℕ) : IsClosed (axialRectangle n) :=
  isClosed_Icc.prod isClosed_Icc

theorem center_mem_axialRectangle {n : ℕ} {u : Site} (hu : u ∈ latticeBox n) :
    HexCells.center u ∈ axialRectangle n := by
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hu
  change (-(n:ℝ) ≤ (u.1:ℝ) ∧ (u.1:ℝ) ≤ n) ∧ (-(n:ℝ) ≤ (u.2:ℝ) ∧ (u.2:ℝ) ≤ n)
  exact_mod_cast hu

/-- Every closed hexagon touching the straight rectangle belongs to the
board. The strict microscopic gap is 1-2/3 in each axial coordinate. -/
theorem cell_meets_axialRectangle {n : ℕ} {u : Site} {p : ℝ × ℝ}
    (hp : p ∈ axialRectangle n) (hcell : p ∈ HexCells.cell u) : u ∈ latticeBox n := by
  have hc := HexCells.coordinate_bounds hcell
  rw [abs_le, abs_le] at hc
  have h1 : -(n:ℝ)-1 < (u.1:ℝ) := by linarith [hp.1.1,hc.1.2]
  have h2 : (u.1:ℝ) < (n:ℝ)+1 := by linarith [hp.1.2,hc.1.1]
  have h3 : -(n:ℝ)-1 < (u.2:ℝ) := by linarith [hp.2.1,hc.2.2]
  have h4 : (u.2:ℝ) < (n:ℝ)+1 := by linarith [hp.2.2,hc.2.1]
  have h1' : -(n:ℤ)-1 < u.1 := by exact_mod_cast h1
  have h2' : u.1 < (n:ℤ)+1 := by exact_mod_cast h2
  have h3' : -(n:ℤ)-1 < u.2 := by exact_mod_cast h3
  have h4' : u.2 < (n:ℤ)+1 := by exact_mod_cast h4
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  omega

def clippedBoxCell (n : ℕ) (u : Site) : Set (ℝ × ℝ) := HexCells.cell u ∩ axialRectangle n

theorem clippedBoxCell_closed (n : ℕ) (u : Site) : IsClosed (clippedBoxCell n u) :=
  (HexCells.isClosed_cell u).inter (axialRectangle_closed n)

theorem clippedBoxCell_convex (n : ℕ) (u : Site) : Convex ℝ (clippedBoxCell n u) :=
  (HexCells.convex_cell u).inter (axialRectangle_convex n)

theorem center_mem_clippedBoxCell {n : ℕ} {u : Site} (hu : u ∈ latticeBox n) :
    HexCells.center u ∈ clippedBoxCell n u :=
  ⟨HexCells.center_mem_cell u, center_mem_axialRectangle hu⟩

theorem clippedBoxCell_pathConnected {n : ℕ} {u : Site} (hu : u ∈ latticeBox n) :
    IsPathConnected (clippedBoxCell n u) :=
  (clippedBoxCell_convex n u).isPathConnected ⟨HexCells.center u, center_mem_clippedBoxCell hu⟩

/-- The literal shared midpoint of adjacent centers survives clipping. -/
theorem adjacent_clippedBoxCells {n : ℕ} {u v : Site}
    (hu : u ∈ latticeBox n) (hv : v ∈ latticeBox n) (hadj : TriangularAdj u v) :
    (clippedBoxCell n u ∩ clippedBoxCell n v).Nonempty := by
  let p : ℝ × ℝ := (((u.1:ℝ)+v.1)/2,((u.2:ℝ)+v.2)/2)
  have hp : p ∈ axialRectangle n := by
    have hcu := center_mem_axialRectangle hu
    have hcv := center_mem_axialRectangle hv
    change ((-(n:ℝ) ≤ p.1 ∧ p.1 ≤ n) ∧ (-(n:ℝ) ≤ p.2 ∧ p.2 ≤ n))
    dsimp [p, HexCells.center] at *
    repeat' constructor
    all_goals linarith [hcu.1.1,hcu.1.2,hcu.2.1,hcu.2.2,hcv.1.1,hcv.1.2,hcv.2.1,hcv.2.2]
  refine ⟨p,⟨HexCells.midpoint_mem_of_adj hadj,hp⟩,?_,hp⟩
  simpa only [p, add_comm] using HexCells.midpoint_mem_of_adj (triangularAdj_symm hadj)

theorem clippedBoxCell_inter_only_neighbors (n : ℕ) (u v : Site)
    (h : (clippedBoxCell n u ∩ clippedBoxCell n v).Nonempty) : u = v ∨ TriangularAdj u v := by
  obtain ⟨p,hpu,hpv⟩ := h
  exact HexCells.intersection_only_neighbors hpu.1 hpv.1

theorem black_clipped_union_eq (n : ℕ) (ω : Configuration) :
    blackCellUnion (clippedBoxCell n) (axialBoxQuad n) ω = globalBlackCells ω ∩ axialRectangle n := by
  ext p
  constructor
  · rintro ⟨u,_hu,hub,hpc,hpr⟩
    exact ⟨⟨u,hub,hpc⟩,hpr⟩
  · rintro ⟨⟨u,hub,hpc⟩,hpr⟩
    exact ⟨u,cell_meets_axialRectangle hpr hpc,hub,hpc,hpr⟩

theorem clipped_walk_pathConnected (n : ℕ) {u v : Site} (p : triangularGraph.Walk u v)
    (hp : ∀ z ∈ p.support, z ∈ latticeBox n) :
    IsPathConnected (walkCellUnion (clippedBoxCell n) p) := by
  induction p with
  | nil => exact clippedBoxCell_pathConnected (hp _ (by simp))
  | @cons a b c hab p ih =>
    have ha := hp a (by simp)
    have hb := hp b (by simp)
    obtain ⟨z,hza,hzb⟩ := adjacent_clippedBoxCells ha hb hab
    apply (clippedBoxCell_pathConnected ha).union
      (ih (fun z hz => hp z (by simp [hz])))
    exact ⟨z,hza,walkCellUnion_start _ p hzb⟩

theorem center_firstSide {n : ℕ} {u : Site} (hu : u ∈ (axialBoxQuad n).firstSide) :
    HexCells.center u ∈ straightLeft n := by
  obtain ⟨hub,hux⟩ := Finset.mem_filter.mp hu
  have hc := center_mem_axialRectangle hub
  refine ⟨?_,hc.2⟩
  change (u.1:ℝ) = -(n:ℝ)
  exact_mod_cast hux

theorem center_secondSide {n : ℕ} {u : Site} (hu : u ∈ (axialBoxQuad n).secondSide) :
    HexCells.center u ∈ straightRight n := by
  obtain ⟨hub,hux⟩ := Finset.mem_filter.mp hu
  have hc := center_mem_axialRectangle hub
  refine ⟨?_,hc.2⟩
  change (u.1:ℝ) = (n:ℝ)
  exact_mod_cast hux

theorem straightLeft_cell_terminal {n : ℕ} {u : Site} {p : ℝ × ℝ}
    (hp : p ∈ straightLeft n) (hc : p ∈ clippedBoxCell n u) :
    u ∈ (axialBoxQuad n).firstSide := by
  have hu := cell_meets_axialRectangle hc.2 hc.1
  have hb := center_mem_axialRectangle hu
  have hr := (HexCells.coordinate_bounds hc.1).1
  rw [abs_le] at hr
  have hlt : (u.1:ℝ) < -(n:ℝ)+1 := by linarith [hp.1,hr.1]
  have hlt' : u.1 < -(n:ℤ)+1 := by exact_mod_cast hlt
  have hlo : -(n:ℤ) ≤ u.1 := by
    have hh : -(n:ℝ) ≤ (u.1:ℝ) := hb.1.1
    exact_mod_cast hh
  exact Finset.mem_filter.mpr ⟨hu,by omega⟩

theorem straightRight_cell_terminal {n : ℕ} {u : Site} {p : ℝ × ℝ}
    (hp : p ∈ straightRight n) (hc : p ∈ clippedBoxCell n u) :
    u ∈ (axialBoxQuad n).secondSide := by
  have hu := cell_meets_axialRectangle hc.2 hc.1
  have hb := center_mem_axialRectangle hu
  have hr := (HexCells.coordinate_bounds hc.1).1
  rw [abs_le] at hr
  have hlt : (n:ℝ)-1 < (u.1:ℝ) := by linarith [hp.1,hr.2]
  have hlt' : (n:ℤ)-1 < u.1 := by exact_mod_cast hlt
  have hhi : u.1 ≤ (n:ℤ) := by
    have hh : (u.1:ℝ) ≤ (n:ℝ) := hb.1.2
    exact_mod_cast hh
  exact Finset.mem_filter.mpr ⟨hu,by omega⟩

/-- Exact crossing equivalence for a genuine straight rectangle. No exterior
completion, finite boundary approximation, or crossing-stability limit is used. -/
theorem straightBox_crossing_iff_graph (n : ℕ) (ω : Configuration) :
    StraightBoxCrossing n ω ↔ (axialBoxQuad n).Crossing ω := by
  constructor
  · rintro ⟨a,ha,b,hb,hjoin⟩
    rw [← black_clipped_union_eq n ω] at hjoin
    obtain ⟨u,huD,huB,hau⟩ := hjoin.source_mem
    obtain ⟨v,hvD,hvB,hbv⟩ := hjoin.target_mem
    have hpath : CellPathCrossing (clippedBoxCell n) (axialBoxQuad n) ω :=
      ⟨u,straightLeft_cell_terminal ha hau,huD,huB,
        v,straightRight_cell_terminal hb hbv,hvD,hvB,a,hau,b,hbv,hjoin⟩
    exact cellCrossing_to_graphCrossing (clippedBoxCell n) (clippedBoxCell_closed n)
      (clippedBoxCell_inter_only_neighbors n) _ ω
      (cellPathCrossing_to_cellCrossing _ _ ω hpath)
  · rintro ⟨u,hu,v,hv,p,hp⟩
    have hc := clipped_walk_pathConnected n p (fun z hz => (hp z hz).1)
    have hcu := center_mem_clippedBoxCell (hp u p.start_mem_support).1
    have hcv := center_mem_clippedBoxCell (hp v p.end_mem_support).1
    have hj := hc.joinedIn (HexCells.center u) (walkCellUnion_start _ p hcu)
      (HexCells.center v) (walkCellUnion_end _ p hcv)
    refine ⟨HexCells.center u,center_firstSide hu,HexCells.center v,center_secondSide hv,?_⟩
    rw [← black_clipped_union_eq n ω]
    exact hj.mono (walkCellUnion_subset _ _ ω p hp)

#print axioms straightBox_crossing_iff_graph

end ExceptionalTimes.PairSquareSewing
