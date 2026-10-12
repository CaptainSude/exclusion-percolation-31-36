import ExceptionalTimes.PolygonCrossingLocality
import Mathlib.Analysis.Convex.PathConnected

/-! A connected crossing in a finite union of closed path-connected pieces
has a path crossing. This is the finite-cell convention bridge; the pieces
may be clipped cells, and no induced graph adjacency is assumed. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

theorem joinedIn_finite_closed_cover {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (F : ι → Set X)
    (hclosed : ∀ i ∈ s, IsClosed (F i))
    (hjoin : ∀ i ∈ s, ∀ a ∈ F i, ∀ b ∈ F i, JoinedIn (F i) a b)
    {K : Set X} (hK : IsPreconnected K)
    (hcover : K ⊆ ⋃ i ∈ s, F i) {a b : X} (ha : a ∈ K) (hb : b ∈ K) :
    JoinedIn (⋃ i ∈ s, F i) a b := by
  classical
  let U := ⋃ i ∈ s, F i
  let H : ι → Prop := fun i => ∃ x ∈ F i, JoinedIn U a x
  let L := ⋃ i ∈ s.filter H, F i
  let R := ⋃ i ∈ s.filter (fun i => ¬ H i), F i
  have hL : IsClosed L := isClosed_biUnion_finset
    (fun i hi => hclosed i (Finset.mem_filter.mp hi).1)
  have hR : IsClosed R := isClosed_biUnion_finset
    (fun i hi => hclosed i (Finset.mem_filter.mp hi).1)
  have htransfer : ∀ i ∈ s, H i → ∀ x ∈ F i, JoinedIn U a x := by
    rintro i hi ⟨y,hy,hay⟩ x hx
    exact hay.trans ((hjoin i hi y hy x hx).mono (fun _ hz => mem_iUnion₂_of_mem hi hz))
  have hKL : a ∈ K ∩ L := by
    obtain ⟨i,hi,hai⟩ := mem_iUnion₂.mp (hcover ha)
    refine ⟨ha,mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hi,?_⟩) hai⟩
    exact ⟨a,hai,JoinedIn.refl (hcover ha)⟩
  by_contra hn
  have hKR : b ∈ K ∩ R := by
    obtain ⟨i,hi,hbi⟩ := mem_iUnion₂.mp (hcover hb)
    refine ⟨hb,mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hi,?_⟩) hbi⟩
    intro hHi
    exact hn (htransfer i hi hHi b hbi)
  have hsub : K ⊆ L ∪ R := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    by_cases hHi : H i
    · exact Or.inl (mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hi,hHi⟩) hxi)
    · exact Or.inr (mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hi,hHi⟩) hxi)
  obtain ⟨x,_hxK,hxL,hxR⟩ := isPreconnected_closed_iff.mp hK L R hL hR hsub ⟨a,hKL⟩ ⟨b,hKR⟩
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hxL
  obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hxR
  exact (Finset.mem_filter.mp hj).2 ⟨x,hxj,
    htransfer i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2 x hxi⟩

/-- The connected closed crossing convention used in the quad topology. -/
def PolygonQuad.ConnectedCrossing (Q : PolygonQuad) (ω : Configuration) : Prop :=
  ∃ K : Set (ℝ × ℝ), IsClosed K ∧ IsConnected K ∧
    K ⊆ globalBlackCells ω ∩ Q.carrier ∧
    (K ∩ Q.left).Nonempty ∧ (K ∩ Q.right).Nonempty

theorem PolygonQuad.connectedCrossing_of_crossing (Q : PolygonQuad) (ω : Configuration)
    (h : Q.Crossing ω) : Q.ConnectedCrossing ω := by
  obtain ⟨a,ha,b,hb,hj⟩ := h
  refine ⟨range hj.somePath,?_,isConnected_range hj.somePath.continuous,?_,?_,?_⟩
  · exact (isCompact_range hj.somePath.continuous).isClosed
  · rintro x ⟨t,rfl⟩
    exact hj.somePath_mem t
  · exact ⟨a,⟨0,hj.somePath.source⟩,ha⟩
  · exact ⟨b,⟨1,hj.somePath.target⟩,hb⟩

theorem PolygonQuad.connectedCrossing_iff_of_convex_cover {ι : Type*} [Fintype ι]
    (Q : PolygonQuad) (piece : ι → Set (ℝ × ℝ))
    (hclosed : ∀ i, IsClosed (piece i)) (hconv : ∀ i, Convex ℝ (piece i))
    (hpieces : Q.carrier = ⋃ i, piece i) (ω : Configuration) :
    Q.ConnectedCrossing ω ↔ Q.Crossing ω := by
  classical
  refine ⟨?_,Q.connectedCrossing_of_crossing ω⟩
  rintro ⟨K,_hKclosed,hK,hsub,⟨a,haK,ha⟩,⟨b,hbK,hb⟩⟩
  let S := Q.support ×ˢ (Finset.univ : Finset ι)
  let s := S.filter (fun i => ω i.1 = true)
  let F : Site × ι → Set (ℝ × ℝ) := fun i => HexCells.cell i.1 ∩ piece i.2
  have hU : (⋃ i ∈ s, F i) = globalBlackCells ω ∩ Q.carrier := by
    ext p
    constructor
    · intro hp
      obtain ⟨⟨v,i⟩,hvi,hpv,hpi⟩ := mem_iUnion₂.mp hp
      have hb := (Finset.mem_filter.mp hvi).2
      refine ⟨⟨v,hb,hpv⟩,?_⟩
      rw [hpieces]
      exact mem_iUnion.mpr ⟨i,hpi⟩
    · rintro ⟨⟨v,hv,hpv⟩,hpQ⟩
      have hvQ := (Q.mem_support v).mpr ⟨p,hpv,hpQ⟩
      rw [hpieces] at hpQ
      obtain ⟨i,hpi⟩ := mem_iUnion.mp hpQ
      have hvi : (v,i) ∈ s := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hvQ,Finset.mem_univ i⟩,hv⟩
      exact mem_iUnion₂_of_mem hvi (show p ∈ F (v,i) from ⟨hpv,hpi⟩)
  refine ⟨a,ha,b,hb,?_⟩
  rw [← hU]
  apply joinedIn_finite_closed_cover s F
  · intro i _hi
    exact (HexCells.isClosed_cell i.1).inter (hclosed i.2)
  · intro i _hi x hx y hy
    exact ((HexCells.convex_cell i.1).inter (hconv i.2)).isPathConnected ⟨x,hx⟩ |>.joinedIn x hx y hy
  · exact hK.isPreconnected
  · rwa [hU]
  · exact haK
  · exact hbK

#print axioms joinedIn_finite_closed_cover
#print axioms PolygonQuad.connectedCrossing_iff_of_convex_cover

end ExceptionalTimes.PairSquareSewing

