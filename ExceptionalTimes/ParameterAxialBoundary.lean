import ExceptionalTimes.ParameterQuadPolygon

/-! A literal finite axial boundary description of a parametrized quad
supplies the polygon and presentation consumed by the forest theorem.
Only its actual segments, side membership, and nonintersection are data. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

def squareSide (s : Bool × Bool) : Set QuadSquare :=
  if s.1 then (if s.2 then squareTop else squareBottom)
  else (if s.2 then squareRight else squareLeft)

theorem mem_squareBoundary_iff (p : QuadSquare) :
    p ∈ quadSquareBoundary ↔ ∃ s, p ∈ squareSide s := by
  simp [quadSquareBoundary,squareSide,squareLeft,squareRight,squareTop,squareBottom,or_assoc]

structure ParameterAxialBoundary (Q : ParameterQuad (ℝ × ℝ)) (E : Type*) where
  edge : E → AxialSegment
  label : E → Bool × Bool
  simple : SimpleSegmentFamily edge
  side_eq : ∀ s p, p ∈ Q.map '' squareSide s ↔ ∃ i, label i=s ∧ (edge i).contains p

theorem AxialSegment.contains_set_eq_segment (s : AxialSegment) :
    {p | s.contains p}=segment ℝ s.first s.last := by
  rw [segment_eq_image_lineMap]
  rfl

theorem AxialSegment.contains_finiteSegments (s : AxialSegment) :
    FiniteSegments {p | s.contains p} := by
  rw [s.contains_set_eq_segment]
  exact ⟨{(s.first,s.last)},by simp⟩

theorem ParameterAxialBoundary.boundary_eq {Q : ParameterQuad (ℝ × ℝ)} {E : Type*}
    (A : ParameterAxialBoundary Q E) :
    Q.map '' quadSquareBoundary=⋃ i, {p | (A.edge i).contains p} := by
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨s,hs⟩ := (mem_squareBoundary_iff x).mp hx
    obtain ⟨i,_hi,hp⟩ := (A.side_eq s (Q.map x)).mp ⟨x,hs,rfl⟩
    exact mem_iUnion.mpr ⟨i,hp⟩
  · intro hp
    obtain ⟨i,hp⟩ := mem_iUnion.mp hp
    obtain ⟨x,hx,rfl⟩ := (A.side_eq (A.label i) p).mpr ⟨i,rfl,hp⟩
    exact ⟨x,(mem_squareBoundary_iff x).mpr ⟨A.label i,hx⟩,rfl⟩

theorem ParameterAxialBoundary.polygonal {Q : ParameterQuad (ℝ × ℝ)} {E : Type*} [Fintype E]
    (A : ParameterAxialBoundary Q E) : FiniteSegments (Q.map '' quadSquareBoundary) := by
  rw [A.boundary_eq]
  have h := FiniteSegments.biUnion Finset.univ (fun i => {p | (A.edge i).contains p})
    (fun i _ => (A.edge i).contains_finiteSegments)
  simpa only [Finset.mem_univ,iUnion_true] using h

noncomputable def ParameterAxialBoundary.polygonQuad (hsource : PublishedInvarianceOfDomain)
    {Q : ParameterQuad (ℝ × ℝ)} {E : Type*} [Fintype E] (A : ParameterAxialBoundary Q E) :
    PolygonQuad := Q.toPolygonQuad hsource A.polygonal

theorem ParameterAxialBoundary.polygonQuad_side (hsource : PublishedInvarianceOfDomain)
    {Q : ParameterQuad (ℝ × ℝ)} {E : Type*} [Fintype E]
    (A : ParameterAxialBoundary Q E) (s : Bool × Bool) :
    (A.polygonQuad hsource).side s=Q.map '' squareSide s := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> rfl

noncomputable def ParameterAxialBoundary.presentation (hsource : PublishedInvarianceOfDomain)
    {Q : ParameterQuad (ℝ × ℝ)} {E : Type*} [Fintype E]
    (A : ParameterAxialBoundary Q E) : AxialPolygonPresentation (A.polygonQuad hsource) E where
  edge := A.edge
  label := A.label
  simple := A.simple
  side_eq := by
    intro s p
    rw [A.polygonQuad_side hsource]
    exact A.side_eq s p

theorem ParameterAxialBoundary.crossing_dictionary (hsource : PublishedInvarianceOfDomain)
    {Q : ParameterQuad (ℝ × ℝ)} {E : Type*} [Fintype E]
    (A : ParameterAxialBoundary Q E)
    (hinteger : ∀ i, ∃ level : ℤ, (A.edge i).level=(level:ℝ)) (ω : Configuration) :
    Q.ClosedCrossing (globalBlackCells ω) ↔ (A.polygonQuad hsource).Crossing ω :=
  Q.closedCrossing_iff_polygonCrossing hsource A.polygonal (A.presentation hsource) hinteger ω

#print axioms ParameterAxialBoundary.presentation
#print axioms ParameterAxialBoundary.crossing_dictionary

end ExceptionalTimes.PairSquareSewing
