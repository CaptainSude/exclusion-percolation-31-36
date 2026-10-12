import ExceptionalTimes.StraightBoxSeparation
import ExceptionalTimes.MixedBoundaryProbes

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

theorem GraphQuad.crossing_eqOn (Q : GraphQuad) {ω η : Configuration}
    (heq : EqOn ω η (Q.domain : Set Site)) : Q.Crossing ω ↔ Q.Crossing η := by
  have hmono {a b : Configuration} (h : EqOn a b (Q.domain : Set Site))
      (hc : Q.Crossing a) : Q.Crossing b := by
    obtain ⟨u,hu,v,hv,p,hp⟩ := hc
    refine ⟨u,hu,v,hv,p,?_⟩
    intro z hz
    have hh := hp z hz
    exact ⟨hh.1,(h hh.1).symm.trans hh.2⟩
  exact ⟨hmono heq,hmono heq.symm⟩

theorem GraphQuad.changed_inside (Q : GraphQuad) {a b : Configuration}
    (h : Q.test a ≠ Q.test b) : ∃ v ∈ Q.domain, a v ≠ b v := by
  by_contra hn
  push Not at hn
  exact h (decide_eq_decide.mpr (Q.crossing_eqOn (fun _ hv => hn _ hv)))

theorem GraphQuad.changed_pocket (Q : GraphQuad) (P : Probe) {a b : Configuration}
    (hab : ∀ v, v ∉ P.pocket → a v=b v) (h : Q.test a ≠ Q.test b) :
    ∃ v ∈ Q.domain, v ∈ P.pocket := by
  obtain ⟨v,hv,hne⟩ := Q.changed_inside h
  exact ⟨v,hv,by by_contra hp; exact hne (hab v hp)⟩

def boxSideProjection (n : ℕ) (s : Bool × Bool) (c : ℝ × ℝ) : ℝ × ℝ :=
  if s.1 then (c.1,if s.2 then (n:ℝ) else -(n:ℝ))
  else (if s.2 then (n:ℝ) else -(n:ℝ),c.2)

theorem boxSideProjection_boundary (n : ℕ) (s : Bool × Bool) (c : ℝ × ℝ) :
    boxSideProjection n s c ∈ (boxHalfPlane n s).boundary := by
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp [boxSideProjection,boxHalfPlane,LatticeHalfPlane.boundary,LatticeHalfPlane.coordinate]

theorem planeMap_norm_vertical (y : ℝ) : ‖HexTiling.planeMap (0,y)‖=|y| := by
  have h := HexTiling.planeMap_normSq (0,y)
  rw [Complex.normSq_eq_norm_sq] at h
  dsimp at h
  nlinarith [norm_nonneg (HexTiling.planeMap (0,y)),abs_nonneg y,sq_abs y]

theorem planeMap_norm_horizontal (x : ℝ) : ‖HexTiling.planeMap (x,0)‖=|x| := by
  have h := HexTiling.planeMap_normSq (x,0)
  rw [Complex.normSq_eq_norm_sq] at h
  dsimp at h
  nlinarith [norm_nonneg (HexTiling.planeMap (x,0)),abs_nonneg x,sq_abs x]

theorem boxSideProjection_distance (n : ℕ) (s : Bool × Bool) (c : ℝ × ℝ)
    {ε : ℝ} (hε : 0≤ε) :
    dist (axialPhysical ε c) (axialPhysical ε (boxSideProjection n s c)) =
      ε*|boxSideSlack n c s| := by
  rw [axialPhysical_dist hε]
  obtain ⟨x,y⟩ := c
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp only [boxSideProjection,boxSideSlack,boxSideCoordinate,Bool.false_eq_true,
      ite_false,ite_true,Prod.mk_sub_mk,sub_self,sub_neg_eq_add,
      planeMap_norm_vertical,planeMap_norm_horizontal]
  all_goals first | rfl | rw [abs_sub_comm]

theorem projection_contact (n : ℕ) (s : Bool × Bool) (c : ℝ × ℝ)
    {ε R : ℝ} (hε : 0≤ε) (h : ε*|boxSideSlack n c s|≤2*R) :
    SideContact ε n R c s := by
  have hd := boxSideProjection_distance n s c hε
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp only [SideContact,Bool.false_eq_true,ite_false,ite_true,NearVertical,NearHorizontal]
  all_goals refine ⟨boxSideProjection n _ c,?_,hd.trans_le h⟩
  all_goals simp [boxSideProjection,signedSide]

theorem boxSideSlack_dist {ε : ℝ} (hε : 0≤ε) (n : ℕ) (s : Bool × Bool) (p q : ℝ × ℝ) :
    ε*|boxSideSlack n p s-boxSideSlack n q s|≤
      2*dist (axialPhysical ε p) (axialPhysical ε q) := by
  have h := physical_coordinate_le hε p q
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp only [boxSideSlack,boxSideCoordinate,Bool.false_eq_true,ite_false,ite_true]
  · have he : p.1+n-(q.1+n)=p.1-q.1 := by ring
    rw [he]
    nlinarith [dist_nonneg (x:=axialPhysical ε p) (y:=axialPhysical ε q)]
  · have he : (n:ℝ)-p.1-(n-q.1)=-(p.1-q.1) := by ring
    rw [he,abs_neg]
    nlinarith [dist_nonneg (x:=axialPhysical ε p) (y:=axialPhysical ε q)]
  · have he : p.2+n-(q.2+n)=p.2-q.2 := by ring
    rw [he]
    nlinarith [dist_nonneg (x:=axialPhysical ε p) (y:=axialPhysical ε q)]
  · have he : (n:ℝ)-p.2-(n-q.2)=-(p.2-q.2) := by ring
    rw [he,abs_neg]
    nlinarith [dist_nonneg (x:=axialPhysical ε p) (y:=axialPhysical ε q)]

/-- A changed crossing supplies a genuine inside-board site. If another
supporting line does not meet the large disk, the center lies strictly
on its inward side, even when the center lies outside the selected side. -/
theorem inward_slack_of_pocket (P : Probe) (n : ℕ) (t : Bool × Bool)
    (hv : ∃ v ∈ latticeBox n, v ∈ P.pocket)
    (hn : ¬SideContact P.mesh n P.outerRadius (HexCells.center P.center) t) :
    2*P.outerRadius < P.mesh*boxSideSlack n (HexCells.center P.center) t := by
  obtain ⟨v,hv,hvp⟩ := hv
  have hin := (mem_rectangle_iff_slacks n (HexCells.center v)).mp (center_mem_axialRectangle hv) t
  have hd := boxSideSlack_dist P.mesh_pos.le n t (HexCells.center P.center) (HexCells.center v)
  have hlow := mul_le_mul_of_nonneg_left
    (neg_le_abs (boxSideSlack n (HexCells.center P.center) t-boxSideSlack n (HexCells.center v) t)) P.mesh_pos.le
  have hinside := mul_nonneg P.mesh_pos.le hin
  have hpocket : dist (axialPhysical P.mesh (HexCells.center P.center))
      (axialPhysical P.mesh (HexCells.center v)) < P.innerRadius/2 := by
    change dist (position P.mesh P.center) (position P.mesh v) < P.innerRadius/2
    rw [dist_comm]
    exact hvp
  have hnot : 2*P.outerRadius < P.mesh*|boxSideSlack n (HexCells.center P.center) t| := by
    by_contra h
    exact hn (projection_contact n t _ P.mesh_pos.le (le_of_not_gt h))
  by_cases hs : 0≤boxSideSlack n (HexCells.center P.center) t
  · simpa only [abs_of_nonneg hs] using hnot
  · rw [abs_of_neg (lt_of_not_ge hs)] at hnot
    linarith [P.radii,P.inner_pos]

#print axioms GraphQuad.changed_pocket
#print axioms inward_slack_of_pocket

end ExceptionalTimes.PairSquareSewing
