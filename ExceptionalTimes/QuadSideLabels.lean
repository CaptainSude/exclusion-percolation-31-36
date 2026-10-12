import ExceptionalTimes.ParameterAxialBoundary
import ExceptionalTimes.FiniteClosedPartition

/-! Side labels are forced by connected geometry away from the four
marked points. In particular no side label is a probabilistic assumption. -/

open Set
open scoped Classical unitInterval
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

theorem mem_quadCorners_iff (p : QuadSquare) :
    p ∈ range quadCorner ↔ (p.1=0 ∨ p.1=1) ∧ (p.2=0 ∨ p.2=1) := by
  constructor
  · rintro ⟨⟨a,b⟩,rfl⟩
    cases a <;> cases b <;> simp [quadCorner]
  · rintro ⟨ha,hb⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact ⟨(false,false),Prod.ext ha.symm hb.symm⟩
    · exact ⟨(false,true),Prod.ext ha.symm hb.symm⟩
    · exact ⟨(true,false),Prod.ext ha.symm hb.symm⟩
    · exact ⟨(true,true),Prod.ext ha.symm hb.symm⟩

theorem squareSide_inter_corner {s t : Bool × Bool} (hst : s≠t) {p : QuadSquare}
    (hs : p ∈ squareSide s) (ht : p ∈ squareSide t) : p ∈ range quadCorner := by
  rw [mem_quadCorners_iff]
  rcases s with ⟨a,b⟩
  rcases t with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [squareSide,squareLeft,squareRight,squareTop,squareBottom]

theorem isClosed_squareSide (s : Bool × Bool) : IsClosed (squareSide s) := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;>
    simp only [squareSide,squareLeft,squareRight,squareTop,squareBottom,
      Bool.false_eq_true,ite_false,ite_true]
  all_goals exact isClosed_eq (by fun_prop) continuous_const

theorem ParameterQuad.side_isClosed (Q : ParameterQuad (ℝ × ℝ)) (s : Bool × Bool) :
    IsClosed (Q.map '' squareSide s) :=
  ((isClosed_squareSide s).isCompact.image Q.continuous).isClosed

theorem ParameterQuad.connected_subset_one_side (Q : ParameterQuad (ℝ × ℝ))
    {K : Set (ℝ × ℝ)} (hK : IsPreconnected K) (hne : K.Nonempty)
    (hboundary : K ⊆ Q.map '' quadSquareBoundary)
    (havoid : ∀ p ∈ K, ∀ b, p≠Q.map (quadCorner b)) :
    ∃ s : Bool × Bool, K ⊆ Q.map '' squareSide s := by
  have hcover : K ⊆ ⋃ s ∈ (Finset.univ : Finset (Bool × Bool)), Q.map '' squareSide s := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := hboundary hp
    obtain ⟨s,hs⟩ := (mem_squareBoundary_iff x).mp hx
    exact mem_iUnion₂_of_mem (Finset.mem_univ s) ⟨x,hs,rfl⟩
  have hdis : ∀ s ∈ (Finset.univ : Finset (Bool × Bool)), ∀ t ∈ Finset.univ,
      s≠t → ∀ p ∈ K, p ∈ Q.map '' squareSide s → p ∉ Q.map '' squareSide t := by
    rintro s _hs t _ht hst p hp ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
    have he : y=x := Q.injective hxy
    subst y
    obtain ⟨b,hb⟩ := squareSide_inter_corner hst hx hy
    exact havoid (Q.map x) hp b (congrArg Q.map hb.symm)
  obtain ⟨s,_hs,hsub⟩ := preconnected_finite_closed_partition Finset.univ
    (fun s => Q.map '' squareSide s) (fun s _ => Q.side_isClosed s) hK hne hcover hdis
  exact ⟨s,hsub⟩

theorem ParameterQuad.closed_edge_one_side (Q : ParameterQuad (ℝ × ℝ))
    {K : Set (ℝ × ℝ)} (hK : IsPreconnected K) (hne : K.Nonempty)
    (hboundary : K ⊆ Q.map '' quadSquareBoundary)
    (havoid : ∀ p ∈ K, ∀ b, p≠Q.map (quadCorner b)) :
    ∃ s : Bool × Bool, closure K ⊆ Q.map '' squareSide s := by
  obtain ⟨s,hs⟩ := Q.connected_subset_one_side hK hne hboundary havoid
  exact ⟨s,closure_minimal hs (Q.side_isClosed s)⟩

#print axioms ParameterQuad.closed_edge_one_side

end ExceptionalTimes.PairSquareSewing
