import ExceptionalTimes.InvarianceOfDomainInput
import ExceptionalTimes.PolygonGridCover
import Mathlib.Topology.TietzeExtension

/-! A homeomorphic polygonal square has the exact carrier and marked arcs
required by PolygonQuad. Only general invariance of domain is external;
compactness, boundary identities and side coordinates are proved here. -/

open Set
open scoped Classical unitInterval
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

def closedQuadSquare : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1

noncomputable def quadSquareHomeomorph : closedQuadSquare ≃ₜ QuadSquare :=
  Homeomorph.Set.prod _ _

theorem closedQuadSquare_regularClosed :
    closure (interior closedQuadSquare)=closedQuadSquare := by
  simp only [closedQuadSquare,interior_prod_eq,interior_Icc,closure_prod_eq,
    closure_Ioo (by norm_num : (0:ℝ)≠1)]

theorem closedQuadSquare_frontier (p : closedQuadSquare) :
    p.val ∈ frontier closedQuadSquare ↔ quadSquareHomeomorph p ∈ quadSquareBoundary := by
  change p.val ∈ frontier (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ↔ _
  rw [frontier_prod_eq,isClosed_Icc.closure_eq,frontier_Icc (by norm_num : (0:ℝ)≤1)]
  have hp := p.property
  change p.val.1 ∈ Icc (0:ℝ) 1 ∧ p.val.2 ∈ Icc (0:ℝ) 1 at hp
  simp only [mem_union,mem_prod,mem_insert_iff,mem_singleton_iff,
    quadSquareBoundary,mem_ofPred_eq,quadSquareHomeomorph,
    Subtype.ext_iff] 
  simp only [hp.1,hp.2,true_and,and_true]
  tauto

namespace ParameterQuad

variable (Q : ParameterQuad (ℝ × ℝ))

noncomputable def closedSquareMap : closedQuadSquare → (ℝ × ℝ) :=
  Q.map ∘ quadSquareHomeomorph

theorem closedSquareMap_embedding : Topology.IsClosedEmbedding Q.closedSquareMap :=
  Q.isClosedEmbedding.comp quadSquareHomeomorph.isClosedEmbedding

theorem closedSquareMap_range : range Q.closedSquareMap=range Q.map :=
  quadSquareHomeomorph.surjective.range_comp Q.map

theorem carrier_regularClosed (hsource : PublishedInvarianceOfDomain) :
    closure (interior (range Q.map))=range Q.map := by
  rw [← Q.closedSquareMap_range]
  exact planarClosedEmbedding_regularClosed hsource closedQuadSquare_regularClosed Q.closedSquareMap_embedding

theorem carrier_frontier (hsource : PublishedInvarianceOfDomain) :
    frontier (range Q.map)=Q.map '' quadSquareBoundary := by
  rw [← Q.closedSquareMap_range,
    planarClosedEmbedding_frontier hsource (isClosed_Icc.prod isClosed_Icc) Q.closedSquareMap_embedding]
  ext y
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨quadSquareHomeomorph p,(closedQuadSquare_frontier p).mp hp,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    refine ⟨quadSquareHomeomorph.symm p,?_,?_⟩
    · exact (closedQuadSquare_frontier _).mpr (by simpa using hp)
    · change Q.map (quadSquareHomeomorph (quadSquareHomeomorph.symm p))=Q.map p
      rw [Homeomorph.apply_symm_apply]

end ParameterQuad

theorem coordinateArc_of_injective_path (f : I → (ℝ × ℝ))
    (hf : Continuous f) (hinj : Function.Injective f) :
    CoordinateArc (range f) (f 0) (f 1) := by
  let c : C(I,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨g,hg⟩ := c.exists_extension' (hf.isClosedEmbedding hinj)
  have hgpoint (t : I) : g (f t)=(t:ℝ) := congrFun hg t
  refine ⟨isCompact_range hf,⟨0,rfl⟩,⟨1,rfl⟩,g,g.continuous,?_,?_,?_⟩
  · rintro x ⟨s,rfl⟩ y ⟨t,rfl⟩ hst
    rw [hgpoint,hgpoint] at hst
    exact congrArg f (Subtype.ext hst)
  · rw [hgpoint,hgpoint]
    norm_num
  · rw [hgpoint 0,hgpoint 1]
    ext x
    constructor
    · rintro ⟨y,⟨t,rfl⟩,rfl⟩
      rw [hgpoint]
      exact t.property
    · intro hx
      exact ⟨f ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩,hgpoint ⟨x,hx⟩⟩

def squareLeft : Set QuadSquare := {p | p.1=0}
def squareRight : Set QuadSquare := {p | p.1=1}
def squareTop : Set QuadSquare := {p | p.2=1}
def squareBottom : Set QuadSquare := {p | p.2=0}

theorem squareBoundary_eq :
    quadSquareBoundary=squareLeft ∪ squareRight ∪ squareTop ∪ squareBottom := by
  ext p
  simp only [quadSquareBoundary,squareLeft,squareRight,squareTop,squareBottom,mem_ofPred_eq,mem_union]
  tauto

theorem square_left_right : Disjoint squareLeft squareRight := by
  apply disjoint_left.mpr
  intro p hp hq
  have he : (0:I)=1 := hp.symm.trans hq
  have hval := congrArg (fun t : I => (t:ℝ)) he
  norm_num at hval

theorem square_top_bottom : Disjoint squareTop squareBottom := by
  apply disjoint_left.mpr
  intro p hp hq
  have he : (1:I)=0 := hp.symm.trans hq
  have hval := congrArg (fun t : I => (t:ℝ)) he
  norm_num at hval

theorem square_left_top : squareLeft ∩ squareTop={(0,1)} := by
  ext p
  simp [squareLeft,squareTop,Prod.ext_iff]

theorem square_right_top : squareRight ∩ squareTop={(1,1)} := by
  ext p
  simp [squareRight,squareTop,Prod.ext_iff]

theorem square_left_bottom : squareLeft ∩ squareBottom={(0,0)} := by
  ext p
  simp [squareLeft,squareBottom,Prod.ext_iff]

theorem square_right_bottom : squareRight ∩ squareBottom={(1,0)} := by
  ext p
  simp [squareRight,squareBottom,Prod.ext_iff]

theorem vertical_square_image (f : QuadSquare → (ℝ × ℝ)) (s : I) :
    f '' {p | p.1=s}=range (fun t : I => f (s,t)) := by
  ext y
  constructor
  · rintro ⟨⟨u,v⟩,rfl,rfl⟩
    exact ⟨v,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨(s,t),rfl,rfl⟩

theorem horizontal_square_image (f : QuadSquare → (ℝ × ℝ)) (s : I) :
    f '' {p | p.2=s}=range (fun t : I => f (t,s)) := by
  ext y
  constructor
  · rintro ⟨⟨u,v⟩,rfl,rfl⟩
    exact ⟨u,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨(t,s),rfl,rfl⟩

theorem ParameterQuad.vertical_arc (Q : ParameterQuad (ℝ × ℝ)) (s : I) :
    CoordinateArc (Q.map '' {p | p.1=s}) (Q.map (s,0)) (Q.map (s,1)) := by
  rw [vertical_square_image]
  apply coordinateArc_of_injective_path
  · exact Q.continuous.comp (continuous_const.prodMk continuous_id)
  · intro t u he
    exact congrArg Prod.snd (Q.injective he)

theorem ParameterQuad.horizontal_arc (Q : ParameterQuad (ℝ × ℝ)) (s : I) :
    CoordinateArc (Q.map '' {p | p.2=s}) (Q.map (0,s)) (Q.map (1,s)) := by
  rw [horizontal_square_image]
  apply coordinateArc_of_injective_path
  · exact Q.continuous.comp (continuous_id.prodMk continuous_const)
  · intro t u he
    exact congrArg Prod.fst (Q.injective he)

/-- Polygonality is precisely the finite-segment condition on the
parametrized boundary. All other PolygonQuad fields are consequences. -/
noncomputable def ParameterQuad.toPolygonQuad (hsource : PublishedInvarianceOfDomain)
    (Q : ParameterQuad (ℝ × ℝ)) (hpolygon : FiniteSegments (Q.map '' quadSquareBoundary)) :
    PolygonQuad where
  carrier := range Q.map
  left := Q.map '' squareLeft
  right := Q.map '' squareRight
  top := Q.map '' squareTop
  bottom := Q.map '' squareBottom
  lowerLeft := Q.map (0,0)
  upperLeft := Q.map (0,1)
  upperRight := Q.map (1,1)
  lowerRight := Q.map (1,0)
  compact := isCompact_range Q.continuous
  regularClosed := Q.carrier_regularClosed hsource
  left_arc := Q.vertical_arc 0
  right_arc := Q.vertical_arc 1
  top_arc := Q.horizontal_arc 1
  bottom_arc := Q.horizontal_arc 0
  frontier_eq := by rw [Q.carrier_frontier hsource,squareBoundary_eq]; simp only [image_union]
  polygonal := (Q.carrier_frontier hsource).symm ▸ hpolygon
  left_right := (disjoint_image_iff Q.injective).mpr square_left_right
  top_bottom := (disjoint_image_iff Q.injective).mpr square_top_bottom
  left_top := by rw [← image_inter Q.injective,square_left_top,image_singleton]
  right_top := by rw [← image_inter Q.injective,square_right_top,image_singleton]
  left_bottom := by rw [← image_inter Q.injective,square_left_bottom,image_singleton]
  right_bottom := by rw [← image_inter Q.injective,square_right_bottom,image_singleton]

/-- The literal closed connected crossing convention for a parametrized
quad and a set of black points. -/
def ParameterQuad.ClosedCrossing (Q : ParameterQuad (ℝ × ℝ)) (black : Set (ℝ × ℝ)) : Prop :=
  ∃ K : Set (ℝ × ℝ), IsClosed K ∧ IsConnected K ∧ K ⊆ black ∩ range Q.map ∧
    (K ∩ Q.map '' squareLeft).Nonempty ∧ (K ∩ Q.map '' squareRight).Nonempty

theorem ParameterQuad.polygon_connectedCrossing (hsource : PublishedInvarianceOfDomain)
    (Q : ParameterQuad (ℝ × ℝ)) (hpolygon : FiniteSegments (Q.map '' quadSquareBoundary))
    (ω : Configuration) :
    (Q.toPolygonQuad hsource hpolygon).ConnectedCrossing ω ↔
      Q.ClosedCrossing (globalBlackCells ω) := Iff.rfl

theorem ParameterQuad.closedCrossing_iff_polygonCrossing
    (hsource : PublishedInvarianceOfDomain) (Q : ParameterQuad (ℝ × ℝ))
    (hpolygon : FiniteSegments (Q.map '' quadSquareBoundary)) {E : Type*}
    (A : AxialPolygonPresentation (Q.toPolygonQuad hsource hpolygon) E)
    (hinteger : ∀ i, ∃ level : ℤ, (A.edge i).level=(level:ℝ)) (ω : Configuration) :
    Q.ClosedCrossing (globalBlackCells ω) ↔ (Q.toPolygonQuad hsource hpolygon).Crossing ω :=
  A.connectedCrossing_iff hinteger ω

#print axioms ParameterQuad.carrier_regularClosed
#print axioms coordinateArc_of_injective_path
#print axioms ParameterQuad.toPolygonQuad
#print axioms ParameterQuad.closedCrossing_iff_polygonCrossing

end ExceptionalTimes.PairSquareSewing
