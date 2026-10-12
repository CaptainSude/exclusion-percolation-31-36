import ExceptionalTimes.UnitGridGeometry

/-! An unlabeled finite unit-grid boundary with marked grid vertices
determines all four side labels and the exact polygon presentation. -/

open Set
open scoped Classical unitInterval
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

def squareSidePoint (s : Bool × Bool) (t : I) : QuadSquare :=
  if s.1 then (t,if s.2 then 1 else 0) else (if s.2 then 1 else 0,t)

theorem continuous_squareSidePoint (s : Bool × Bool) : Continuous (squareSidePoint s) := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b
  · change Continuous (fun t : I => ((0:I),t))
    fun_prop
  · change Continuous (fun t : I => ((1:I),t))
    fun_prop
  · change Continuous (fun t : I => (t,(0:I)))
    fun_prop
  · change Continuous (fun t : I => (t,(1:I)))
    fun_prop

theorem range_squareSidePoint (s : Bool × Bool) : range (squareSidePoint s)=squareSide s := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b
  · change range (fun t : I => ((0:I),t))={p | p.1=0}
    ext p
    constructor
    · rintro ⟨t,rfl⟩; rfl
    · intro h; exact ⟨p.2,Prod.ext h.symm rfl⟩
  · change range (fun t : I => ((1:I),t))={p | p.1=1}
    ext p
    constructor
    · rintro ⟨t,rfl⟩; rfl
    · intro h; exact ⟨p.2,Prod.ext h.symm rfl⟩
  · change range (fun t : I => (t,(0:I)))={p | p.2=0}
    ext p
    constructor
    · rintro ⟨t,rfl⟩; rfl
    · intro h; exact ⟨p.1,Prod.ext rfl h.symm⟩
  · change range (fun t : I => (t,(1:I)))={p | p.2=1}
    ext p
    constructor
    · rintro ⟨t,rfl⟩; rfl
    · intro h; exact ⟨p.1,Prod.ext rfl h.symm⟩

theorem squareSidePoint_not_corner (s : Bool × Bool) {t : I}
    (ht : t ∈ Ioo (0:I) 1) : squareSidePoint s t ∉ range quadCorner := by
  rw [mem_quadCorners_iff]
  have ht0 : t≠0 := ne_of_gt ht.1
  have ht1 : t≠1 := ne_of_lt ht.2
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> simp [squareSidePoint,ht0,ht1]

theorem unitInterval_closed_of_open {X : Type*} [TopologicalSpace X]
    {f : I → X} (hf : Continuous f) {K : Set X} (hK : IsClosed K)
    (hsub : ∀ t ∈ Ioo (0:I) 1, f t ∈ K) : ∀ t, f t ∈ K := by
  have hc : closure (Ioo (0:I) 1) ⊆ f ⁻¹' K := closure_minimal hsub (hK.preimage hf)
  rw [closure_Ioo (by norm_num : (0:I)≠1),← unitInterval.univ_eq_Icc] at hc
  exact fun t => hc (mem_univ t)

theorem ParameterQuad.side_subset_closed (Q : ParameterQuad (ℝ × ℝ)) (s : Bool × Bool)
    {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hsub : ∀ p ∈ Q.map '' squareSide s, (∀ b, p≠Q.map (quadCorner b)) → p ∈ K) :
    Q.map '' squareSide s ⊆ K := by
  have ht : ∀ t, Q.map (squareSidePoint s t) ∈ K := by
    apply unitInterval_closed_of_open (Q.continuous.comp (continuous_squareSidePoint s)) hK
    intro t ht
    apply hsub _
    · refine ⟨squareSidePoint s t,?_,rfl⟩
      rw [← range_squareSidePoint]
      exact mem_range_self t
    · intro b he
      exact squareSidePoint_not_corner s ht ⟨b,(Q.injective he).symm⟩
  rintro p ⟨x,hx,rfl⟩
  rw [← range_squareSidePoint] at hx
  obtain ⟨t,rfl⟩ := hx
  exact ht t

/-- Literal grid data: the boundary is a finite union of integer unit
edges and the four marked vertices lie on the integer grid. Side labels,
polygon regularity, and the crossing dictionary are derived below. -/
structure ParameterUnitBoundary (Q : ParameterQuad (ℝ × ℝ)) where
  edges : Finset UnitGridEdge
  boundary : ∀ p, p ∈ Q.map '' quadSquareBoundary ↔ ∃ e ∈ edges, p ∈ e.carrier
  marked : ∀ b, ∃ v : Site, Q.map (quadCorner b)=HexCells.center v

namespace ParameterUnitBoundary

variable {Q : ParameterQuad (ℝ × ℝ)} (A : ParameterUnitBoundary Q)

theorem edge_boundary (e : A.edges) : e.val.carrier ⊆ Q.map '' quadSquareBoundary := by
  intro p hp
  exact (A.boundary p).mpr ⟨e.val,e.property,hp⟩

noncomputable def label (e : A.edges) : Bool × Bool :=
  Classical.choose (e.val.quad_side Q (A.edge_boundary e) A.marked)

theorem label_subset (e : A.edges) : e.val.carrier ⊆ Q.map '' squareSide (A.label e) :=
  Classical.choose_spec (e.val.quad_side Q (A.edge_boundary e) A.marked)

theorem label_eq_of_avoids_corners (e : A.edges) {s : Bool × Bool} {p : ℝ × ℝ}
    (hp : p ∈ e.val.carrier) (hs : p ∈ Q.map '' squareSide s)
    (havoid : ∀ b, p≠Q.map (quadCorner b)) : A.label e=s := by
  by_contra hn
  obtain ⟨x,hx,hpx⟩ := A.label_subset e hp
  obtain ⟨y,hy,hpy⟩ := hs
  have hxy : x=y := Q.injective (hpx.trans hpy.symm)
  subst y
  obtain ⟨b,hb⟩ := squareSide_inter_corner hn hx hy
  exact havoid b (hpx.symm.trans (congrArg Q.map hb.symm))

theorem side_eq (s : Bool × Bool) (p : ℝ × ℝ) :
    p ∈ Q.map '' squareSide s ↔ ∃ e : A.edges, A.label e=s ∧ e.val.segment.contains p := by
  constructor
  · intro hp
    let K : Set (ℝ × ℝ) := ⋃ e : {e : A.edges // A.label e=s}, e.val.val.carrier
    have hK : IsClosed K := isClosed_iUnion_of_finite (fun e => e.val.val.carrier_closed)
    have hsub : Q.map '' squareSide s ⊆ K := by
      apply Q.side_subset_closed s hK
      intro q hq havoid
      have hboundary : q ∈ Q.map '' quadSquareBoundary := by
        obtain ⟨x,hx,rfl⟩ := hq
        exact ⟨x,(mem_squareBoundary_iff x).mpr ⟨s,hx⟩,rfl⟩
      obtain ⟨e,he,hqe⟩ := (A.boundary q).mp hboundary
      have hlabel : A.label ⟨e,he⟩=s := A.label_eq_of_avoids_corners ⟨e,he⟩ hqe hq havoid
      exact mem_iUnion.mpr ⟨⟨⟨e,he⟩,hlabel⟩,hqe⟩
    obtain ⟨e,he⟩ := mem_iUnion.mp (hsub hp)
    refine ⟨e.val,e.property,?_⟩
    change p ∈ {p | e.val.val.segment.contains p}
    rw [e.val.val.segment_carrier]
    exact he
  · rintro ⟨e,he,hp⟩
    rw [← he]
    apply A.label_subset e
    rw [← e.val.segment_carrier]
    exact hp

noncomputable def presentation : ParameterAxialBoundary Q A.edges where
  edge := fun e => e.val.segment
  label := A.label
  simple := UnitGridEdge.simple A.edges
  side_eq := A.side_eq

theorem presentation_integer (e : A.edges) :
    ∃ z : ℤ, (A.presentation.edge e).level=(z:ℝ) := e.val.segment_level_integer

/-- The crossing tests consumed by the finite forest bound are exactly
the original closed connected crossing tests of the grid quad. -/
theorem crossing_dictionary (hsource : PublishedInvarianceOfDomain) (ω : Configuration) :
    Q.ClosedCrossing (globalBlackCells ω) ↔ (A.presentation.polygonQuad hsource).Crossing ω :=
  A.presentation.crossing_dictionary hsource A.presentation_integer ω

#print axioms presentation
#print axioms crossing_dictionary

end ParameterUnitBoundary
end ExceptionalTimes.PairSquareSewing
