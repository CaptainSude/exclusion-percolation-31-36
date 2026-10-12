import ExceptionalTimes.QuadSideLabels

/-! Literal unit axial edges of the integer grid. Their open cores avoid
every grid vertex, so marked grid vertices cannot interrupt a side label. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

structure UnitGridEdge where
  anchor : Site
  horizontal : Bool
  deriving DecidableEq

namespace UnitGridEdge

def first (e : UnitGridEdge) : ℝ × ℝ := HexCells.center e.anchor

def last (e : UnitGridEdge) : ℝ × ℝ :=
  if e.horizontal then ((e.anchor.1:ℝ)+1,(e.anchor.2:ℝ))
  else ((e.anchor.1:ℝ),(e.anchor.2:ℝ)+1)

def carrier (e : UnitGridEdge) : Set (ℝ × ℝ) :=
  if e.horizontal then Icc (e.anchor.1:ℝ) (e.anchor.1+1) ×ˢ {(e.anchor.2:ℝ)}
  else {(e.anchor.1:ℝ)} ×ˢ Icc (e.anchor.2:ℝ) (e.anchor.2+1)

def core (e : UnitGridEdge) : Set (ℝ × ℝ) :=
  if e.horizontal then Ioo (e.anchor.1:ℝ) (e.anchor.1+1) ×ˢ {(e.anchor.2:ℝ)}
  else {(e.anchor.1:ℝ)} ×ˢ Ioo (e.anchor.2:ℝ) (e.anchor.2+1)

theorem first_ne_last (e : UnitGridEdge) : e.first≠e.last := by
  intro he
  cases hh : e.horizontal
  · have he' := congrArg Prod.snd he
    simp only [first,last,HexCells.center,hh,Bool.false_eq_true,ite_false] at he'
    linarith
  · have he' := congrArg Prod.fst he
    simp only [first,last,HexCells.center,hh,ite_true] at he'
    linarith

noncomputable def segment (e : UnitGridEdge) : AxialSegment where
  first := e.first
  last := e.last
  horizontal := e.horizontal
  parallel := by cases hh : e.horizontal <;> simp [first,last,HexCells.center,hh]
  nondegenerate := e.first_ne_last

theorem core_convex (e : UnitGridEdge) : Convex ℝ e.core := by
  cases hh : e.horizontal <;> simp only [core,hh,Bool.false_eq_true,ite_false,ite_true]
  · exact (convex_singleton _).prod (convex_Ioo _ _)
  · exact (convex_Ioo _ _).prod (convex_singleton _)

theorem core_nonempty (e : UnitGridEdge) : e.core.Nonempty := by
  cases hh : e.horizontal <;> simp only [core,hh,Bool.false_eq_true,ite_false,ite_true]
  · exact ⟨((e.anchor.1:ℝ),(e.anchor.2:ℝ)+1/2),rfl,by constructor <;> linarith⟩
  · exact ⟨((e.anchor.1:ℝ)+1/2,(e.anchor.2:ℝ)),by constructor <;> linarith,rfl⟩

theorem closure_core (e : UnitGridEdge) : closure e.core=e.carrier := by
  cases hh : e.horizontal <;> simp only [core,carrier,hh,Bool.false_eq_true,ite_false,ite_true,
    closure_prod_eq,isClosed_singleton.closure_eq,
    closure_Ioo (by linarith : (e.anchor.1:ℝ)≠e.anchor.1+1),
    closure_Ioo (by linarith : (e.anchor.2:ℝ)≠e.anchor.2+1)]

theorem core_subset (e : UnitGridEdge) : e.core ⊆ e.carrier :=
  e.closure_core ▸ subset_closure

theorem core_avoids_grid (e : UnitGridEdge) {p : ℝ × ℝ} (hp : p ∈ e.core)
    (v : Site) : p≠HexCells.center v := by
  intro he
  subst p
  cases hh : e.horizontal
  · simp only [core,hh,Bool.false_eq_true,ite_false,mem_prod,mem_singleton_iff] at hp
    exact not_integer_between e.anchor.2 hp.2.1 hp.2.2 ⟨v.2,rfl⟩
  · simp only [core,hh,ite_true,mem_prod,mem_singleton_iff] at hp
    exact not_integer_between e.anchor.1 hp.1.1 hp.1.2 ⟨v.1,rfl⟩

theorem segment_carrier (e : UnitGridEdge) : {p | e.segment.contains p}=e.carrier := by
  ext p
  cases hh : e.horizontal
  · simp only [carrier,hh,Bool.false_eq_true,ite_false]
    constructor
    · rintro ⟨t,ht,hp⟩
      have h1 := congrArg Prod.fst hp
      have h2 := congrArg Prod.snd hp
      simp only [segment,AxialSegment.point,first,last,HexCells.center,hh,Bool.false_eq_true,
        ite_false,AffineMap.lineMap_apply_module,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
        Prod.smul_snd,smul_eq_mul] at h1 h2
      change p.1=(e.anchor.1:ℝ) ∧ (e.anchor.2:ℝ)≤p.2 ∧ p.2≤e.anchor.2+1
      constructor
      · nlinarith
      · constructor <;> nlinarith [ht.1,ht.2]
    · intro hp
      change p.1=(e.anchor.1:ℝ) ∧ (e.anchor.2:ℝ)≤p.2 ∧ p.2≤e.anchor.2+1 at hp
      refine ⟨p.2-e.anchor.2,⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩,?_⟩
      apply Prod.ext <;>
        simp [segment,AxialSegment.point,first,last,HexCells.center,hh,
          AffineMap.lineMap_apply_module,hp.1] <;> ring
  · simp only [carrier,hh,ite_true]
    constructor
    · rintro ⟨t,ht,hp⟩
      have h1 := congrArg Prod.fst hp
      have h2 := congrArg Prod.snd hp
      simp only [segment,AxialSegment.point,first,last,HexCells.center,hh,
        ite_true,AffineMap.lineMap_apply_module,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
        Prod.smul_snd,smul_eq_mul] at h1 h2
      change ((e.anchor.1:ℝ)≤p.1 ∧ p.1≤e.anchor.1+1) ∧ p.2=(e.anchor.2:ℝ)
      constructor
      · constructor <;> nlinarith [ht.1,ht.2]
      · nlinarith
    · intro hp
      change ((e.anchor.1:ℝ)≤p.1 ∧ p.1≤e.anchor.1+1) ∧ p.2=(e.anchor.2:ℝ) at hp
      refine ⟨p.1-e.anchor.1,⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,?_⟩
      apply Prod.ext <;>
        simp [segment,AxialSegment.point,first,last,HexCells.center,hh,
          AffineMap.lineMap_apply_module,hp.2] <;> ring

theorem quad_side (Q : ParameterQuad (ℝ × ℝ)) (e : UnitGridEdge)
    (hboundary : e.carrier ⊆ Q.map '' quadSquareBoundary)
    (hmarked : ∀ b, ∃ v : Site, Q.map (quadCorner b)=HexCells.center v) :
    ∃ s : Bool × Bool, e.carrier ⊆ Q.map '' squareSide s := by
  have havoid : ∀ p ∈ e.core, ∀ b, p≠Q.map (quadCorner b) := by
    intro p hp b
    obtain ⟨v,hv⟩ := hmarked b
    rw [hv]
    exact e.core_avoids_grid hp v
  simpa only [e.closure_core] using
    Q.closed_edge_one_side e.core_convex.isPreconnected e.core_nonempty
      (e.core_subset.trans hboundary) havoid

#print axioms segment_carrier
#print axioms quad_side

end UnitGridEdge
end ExceptionalTimes.PairSquareSewing
