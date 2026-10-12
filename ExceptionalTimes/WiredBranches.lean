import ExceptionalTimes.CycleBranches
import ExceptionalTimes.SeparatingCircuitReach
import ExceptionalTimes.RadialFourArmProbe

/-! Four actual untrimmed branches from radial cell pivotality. The white
branches meet again only at a vertex far outside the local probe. Cyclic
order and proper circular trimming are still separate obligations. -/

namespace ExceptionalTimes.WiredBranches

open WiredBoundary HoleFilling WiredPivotal

structure Branches (ω : Configuration) (D : Finset Site) (r R : ℕ)
    (pivot far outer : Site) where
  blackIn : triangularGraph.Walk pivot (0,0)
  blackOut : triangularGraph.Walk pivot outer
  whiteFirst : triangularGraph.Walk pivot far
  whiteSecond : triangularGraph.Walk pivot far
  blackIn_path : blackIn.IsPath
  blackOut_path : blackOut.IsPath
  whiteFirst_path : whiteFirst.IsPath
  whiteSecond_path : whiteSecond.IsPath
  white_cycle : ∃ a : Site,∃ c : triangularGraph.Walk a a,c.IsCycle ∧
    (∀ z,z∈c.support ↔ z∈whiteFirst.support ∨ z∈whiteSecond.support)
  white_separates : SeparatesFromInfinity (latticeBox r : Set Site)
    {z | z∈whiteFirst.support ∨ z∈whiteSecond.support}
  white_annulus : ∀ z,(z∈whiteFirst.support ∨ z∈whiteSecond.support) →
    z∉latticeBox r ∧ z∈latticeBox (R+1)
  black_intersection : ∀ z∈blackIn.support,z∈blackOut.support → z=pivot
  white_intersection : ∀ z∈whiteFirst.support,z∈whiteSecond.support → z=pivot ∨ z=far
  opposite_intersection : ∀ z, (z∈blackIn.support ∨ z∈blackOut.support) →
    (z∈whiteFirst.support ∨ z∈whiteSecond.support) → z=pivot
  black_color : ∀ z, (z∈blackIn.support ∨ z∈blackOut.support) → z∉D →
    z∉latticeBox r → z∈latticeBox (R+1) → ω z=true
  white_color : ∀ z, (z∈whiteFirst.support ∨ z∈whiteSecond.support) → z∉D → ω z=false

theorem cell_pivotal_branches (boundaryInput : FiniteClusterBoundaryCircuit)
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
  obtain ⟨η,v,hv,hext,w,cbase,p,c,hw,hp,hc,hblack,hwhite,hsep,hvp,hvc,hunique,_⟩ :=
    cell_pivotal_wired_witnesses boundaryInput hrR D ω (htest ▸ hpiv)
  obtain ⟨s,hs,hfar⟩ := SeparatingCircuitReach.separating_set_euclidean_reach hsep
    (origin_mem_box r) x
  have hvs : v≠s := by
    intro heq
    subst s
    exact (not_lt_of_ge hfar) (hnear v hv)
  obtain ⟨b₀,b₁,hb₀,hb₁,hb₀p,hb₁p,hbb⟩ := CycleBranches.path_two_branches p hp hvp
  obtain ⟨w₀,w₁,hw₀,hw₁,hw₀c,hw₁c,hww,hcover⟩ := CycleBranches.cycle_two_paths_from_member c hc hvc hs hvs
  refine ⟨v,hv,s,w,hfar,hw,⟨{
    blackIn := b₀
    blackOut := b₁
    whiteFirst := w₀
    whiteSecond := w₁
    blackIn_path := hb₀
    blackOut_path := hb₁
    whiteFirst_path := hw₀
    whiteSecond_path := hw₁
    white_cycle := ⟨cbase,c,hc,fun z => ⟨hcover z,fun h =>
      h.elim (fun hz => hw₀c hz) (fun hz => hw₁c hz)⟩⟩
    white_separates := ?_
    white_annulus := ?_
    black_intersection := hbb
    white_intersection := hww
    opposite_intersection := ?_
    black_color := ?_
    white_color := ?_ }⟩⟩
  · obtain ⟨K,hK,hcut⟩ := hsep
    refine ⟨K,hK,?_⟩
    intro u hu t ht walk
    obtain ⟨z,hzw,hzc⟩ := hcut u hu t ht walk
    exact ⟨z,hzw,hcover z hzc⟩
  · intro z hz
    have hzc := hz.elim (fun h => hw₀c h) (fun h => hw₁c h)
    exact ⟨(hwhite z hzc).1,(hwhite z hzc).2.1⟩
  · intro z hb hw'
    exact hunique z (hb.elim (fun h => hb₀p h) (fun h => hb₁p h))
      (hw'.elim (fun h => hw₀c h) (fun h => hw₁c h))
  · intro z hb hzD hzr hzR
    have hzcol := hblack z (hb.elim (fun h => hb₀p h) (fun h => hb₁p h))
    simp only [wireBoth,hzr,hzR,not_true_eq_false,false_or,↓reduceIte] at hzcol
    exact (hext true z hzD).symm.trans hzcol
  · intro z hw' hzD
    have hzcol := (hwhite z (hw'.elim (fun h => hw₀c h) (fun h => hw₁c h))).2.2
    exact (hext false z hzD).symm.trans hzcol

#print axioms cell_pivotal_branches

open MesoscopicCells

theorem dimerCell_near_anchor {B : Type*} [Fintype B]
    (slot : B×Fin 2 ↪ Site) (z : Site) (m d : ℕ)
    (hm : 0<m) (hd : d≤m) (hz : z∈latticeBox d)
    (hp : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (c : Site) (hc : c∈occupied m slot)
    (hscale : 32*m≤anchorRadius m slot c) :
    ∀ v∈dimerCell m slot c,
      ‖triangularEmbedding (v-anchor m slot c)‖ <
        (latticeRadius (anchor m slot c) : ℝ)/2 := by
  intro v hv
  have hnorm := triangularEmbedding_norm_le_of_mem_box
    (dimerCell_diameter m hm slot z hz hp hv (anchor_mem m slot c hc))
  have hd' : (d : ℝ)≤m := by exact_mod_cast hd
  have hm' : 0<(m : ℝ) := by exact_mod_cast hm
  have hscale' : 32*(m : ℝ)≤latticeRadius (anchor m slot c) := by
    exact_mod_cast hscale
  push_cast at hnorm
  linarith

theorem dimerCell_pivotal_branches (boundaryInput : FiniteClusterBoundaryCircuit)
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
    (dimerCell_near_anchor slot z m d hm hd hz hp c hc hscale) hpiv

#print axioms dimerCell_pivotal_branches

end ExceptionalTimes.WiredBranches
