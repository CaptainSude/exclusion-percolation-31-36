import ExceptionalTimes.PlaneWiredPivotal
import ExceptionalTimes.PlaneCycleBranches
import ExceptionalTimes.WiredBranches

/-! Actual radial pivotal branches retaining the complete white polygon and
its planar enclosure. The only boundary input is the explicitly stated
published plane-enclosing finite-cluster circuit theorem. Cyclic order of
the four outgoing branches and circular trimming are not asserted here.
-/

namespace ExceptionalTimes.PlaneBranches

open WiredBoundary HoleFilling WiredPivotal TriangularPlane Set
open PairSquareSewing

/-- The old branch witness with the actual joined white cycle and the
different complementary components of the two black endpoints retained. -/
structure Branches (ω : Configuration) (D : Finset Site) (r R : ℕ)
    (pivot far outer : Site) extends WiredBranches.Branches ω D r R pivot far outer where
  white_joined_cycle : (whiteFirst.append whiteSecond.reverse).IsCycle
  origin_not_white : point (0,0)∉walkTrace whiteFirst∪walkTrace whiteSecond
  outer_not_white : point outer∉walkTrace whiteFirst∪walkTrace whiteSecond
  origin_component_bounded : Bornology.IsBounded
    (connectedComponentIn (walkTrace whiteFirst∪walkTrace whiteSecond)ᶜ (point (0,0)))
  outer_outside_origin_component : point outer∉
    connectedComponentIn (walkTrace whiteFirst∪walkTrace whiteSecond)ᶜ (point (0,0))

theorem cell_pivotal_branches (boundaryInput : PlaneClusterBoundaryCircuit)
    {r R : ℕ} (hrR : r≤R) (D : Finset Site) (ω : Configuration) (x : Site)
    (hnear : ∀ v∈D,‖triangularEmbedding (v-x)‖<(latticeRadius x : ℝ)/2)
    (hpiv : CellInterpolation.CellPivotal (HoleFilling.wiredArmTest r R) D ω) :
    ∃ v∈D, ∃ s w : Site,
      (latticeRadius x : ℝ)/2≤‖triangularEmbedding (s-x)‖ ∧
      w∉latticeBox (R+1) ∧ Nonempty (Branches ω D r R v s w) := by
  classical
  have htest : WiredPivotal.wiredArmTest r R=HoleFilling.wiredArmTest r R := by
    funext η
    simp [WiredPivotal.wiredArmTest,HoleFilling.wiredArmTest]
  obtain ⟨η,v,hv,hext,w,cbase,p,c,hw,hp,hc,hblack,hwhite,hsep,
    hbounded,houtside,hvp,hvc,hunique,_⟩ :=
    cell_pivotal_plane_witnesses boundaryInput hrR D ω (htest ▸ hpiv)
  obtain ⟨s,hs,hfar⟩ := SeparatingCircuitReach.separating_set_euclidean_reach hsep
    (origin_mem_box r) x
  have hvs : v≠s := by
    intro heq
    subst s
    exact (not_lt_of_ge hfar) (hnear v hv)
  obtain ⟨b₀,b₁,hb₀,hb₁,hb₀p,hb₁p,hbb⟩ := CycleBranches.path_two_branches p hp hvp
  obtain ⟨w₀,w₁,hw₀,hw₁,hw₀c,hw₁c,hww,hcover,htrace,hcycle⟩ :=
    plane_cycle_two_paths c hc hvc hs hvs
  have hwhite_support (z : Site) (hz : z∈w₀.support ∨ z∈w₁.support) : z∈c.support :=
    hz.elim (fun h => hw₀c h) (fun h => hw₁c h)
  have horigin : point (0,0)∉walkTrace w₀∪walkTrace w₁ := by
    rw [←htrace,point_mem_walkTrace_iff]
    intro h
    exact (hwhite (0,0) h).1 (origin_mem_box r)
  have houter : point w∉walkTrace w₀∪walkTrace w₁ := by
    rw [←htrace,point_mem_walkTrace_iff]
    intro h
    exact hw (hwhite w h).2.1
  refine ⟨v,hv,s,w,hfar,hw,⟨{
    blackIn := b₀
    blackOut := b₁
    whiteFirst := w₀
    whiteSecond := w₁
    blackIn_path := hb₀
    blackOut_path := hb₁
    whiteFirst_path := hw₀
    whiteSecond_path := hw₁
    white_cycle := ⟨cbase,c,hc,fun z => ⟨hcover z,hwhite_support z⟩⟩
    white_separates := ?_
    white_annulus := ?_
    black_intersection := hbb
    white_intersection := hww
    opposite_intersection := ?_
    black_color := ?_
    white_color := ?_
    white_joined_cycle := hcycle
    origin_not_white := horigin
    outer_not_white := houter
    origin_component_bounded := ?_
    outer_outside_origin_component := ?_ }⟩⟩
  · obtain ⟨K,hK,hcut⟩ := hsep
    refine ⟨K,hK,?_⟩
    intro u hu t ht walk
    obtain ⟨z,hzw,hzc⟩ := hcut u hu t ht walk
    exact ⟨z,hzw,hcover z hzc⟩
  · intro z hz
    exact ⟨(hwhite z (hwhite_support z hz)).1,(hwhite z (hwhite_support z hz)).2.1⟩
  · intro z hb hw'
    exact hunique z (hb.elim (fun h => hb₀p h) (fun h => hb₁p h)) (hwhite_support z hw')
  · intro z hb hzD hzr hzR
    have hzcol := hblack z (hb.elim (fun h => hb₀p h) (fun h => hb₁p h))
    simp only [wireBoth,hzr,hzR,not_true_eq_false,false_or,↓reduceIte] at hzcol
    exact (hext true z hzD).symm.trans hzcol
  · intro z hw' hzD
    have hzcol := (hwhite z (hwhite_support z hw')).2.2
    exact (hext false z hzD).symm.trans hzcol
  · rwa [←htrace]
  · rwa [←htrace]

/-- Geometric black/white intersections remain confined to the pivot. -/
theorem Branches.opposite_trace_intersection
    {ω : Configuration} {D : Finset Site} {r R : ℕ} {v s w : Site}
    (B : Branches ω D r R v s w) {z : ℝ×ℝ}
    (hb : z∈walkTrace B.blackIn∪walkTrace B.blackOut)
    (hw : z∈walkTrace B.whiteFirst∪walkTrace B.whiteSecond) : z=point v := by
  rcases hb with hb | hb <;> rcases hw with hw | hw
  · exact walkTrace_intersection_only B.blackIn B.whiteFirst
      (fun a ha ht => B.opposite_intersection a (Or.inl ha) (Or.inl ht)) hb hw
  · exact walkTrace_intersection_only B.blackIn B.whiteSecond
      (fun a ha ht => B.opposite_intersection a (Or.inl ha) (Or.inr ht)) hb hw
  · exact walkTrace_intersection_only B.blackOut B.whiteFirst
      (fun a ha ht => B.opposite_intersection a (Or.inr ha) (Or.inl ht)) hb hw
  · exact walkTrace_intersection_only B.blackOut B.whiteSecond
      (fun a ha ht => B.opposite_intersection a (Or.inr ha) (Or.inr ht)) hb hw

open MesoscopicCells

theorem dimerCell_pivotal_branches (boundaryInput : PlaneClusterBoundaryCircuit)
    {B : Type*} [Fintype B] (slot : B×Fin 2 ↪ Site) (z : Site) (m d r R : ℕ)
    (hm : 0<m) (hd : d≤m) (hz : z∈latticeBox d)
    (hp : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (hrR : r≤R) (c : Site) (hc : c∈occupied m slot)
    (hscale : 32*m≤anchorRadius m slot c) (ω : Configuration)
    (hpiv : CellInterpolation.CellPivotal (HoleFilling.wiredArmTest r R)
      (dimerCell m slot c) ω) :
    ∃ v∈dimerCell m slot c, ∃ s w : Site,
      (anchorRadius m slot c : ℝ)/2≤‖triangularEmbedding (s-anchor m slot c)‖ ∧
      w∉latticeBox (R+1) ∧ Nonempty (Branches ω (dimerCell m slot c) r R v s w) :=
  cell_pivotal_branches boundaryInput hrR _ ω _
    (WiredBranches.dimerCell_near_anchor slot z m d hm hd hz hp c hc hscale) hpiv

#print axioms cell_pivotal_branches
#print axioms Branches.opposite_trace_intersection
#print axioms dimerCell_pivotal_branches

end ExceptionalTimes.PlaneBranches
