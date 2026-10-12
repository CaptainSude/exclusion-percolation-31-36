import ExceptionalTimes.WiredBranchTrimming

/-! Fully instantiated circular path witnesses for the actual mesoscopic
pivotal cell. No locality, endpoint, color, or distance premise remains.
The alternating cyclic-order theorem is still a separate obligation. -/

namespace ExceptionalTimes.RadialBranchWitness

open PairSquareSewing MesoscopicCells RadialFourArmProbe WiredBranches HoleFilling

theorem cell_pivotal_trimmed (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    {B : Type*} [Fintype B] (slot : B×Fin 2 ↪ Site) (z : Site) (K m d r R : ℕ)
    (hK : 2≤K) (hm : 0<m) (hd : d≤m) (hz : z∈latticeBox d)
    (hp : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (c : Site) (hc : c∈occupied m slot)
    (hscale : 8192*K*m≤anchorRadius m slot c)
    (hr : 0<r) (hR : 16*r≤R) (hdr : 2*d≤r)
    (hx : anchor m slot c∈annularSites (2*r-d) (R/2+d))
    (ω : Configuration)
    (hpiv : CellInterpolation.CellPivotal (wiredArmTest r R) (dimerCell m slot c) ω) :
    let P := probe (anchor m slot c) K m d hK hm hd hscale
    ∃ v∈dimerCell m slot c,∃ s w : Site,∃ b : Branches ω (dimerCell m slot c) r R v s w,
      Nonempty (TrimmedBranches P ω (dimerCell m slot c) r R b) := by
  let P := probe (anchor m slot c) K m d hK hm hd hscale
  have hscale' : 32*m≤anchorRadius m slot c := by nlinarith
  obtain ⟨v,hv,s,w,hfar,hw,⟨b⟩⟩ := dimerCell_pivotal_branches boundaryInput slot z m d r R
    hm hd hz hp (by omega) c hc hscale' ω hpiv
  have hball := probe_closed_ball_bulk (anchor m slot c) K m d r R hK hm hd hscale
    hr hR hdr hx
  have hzero : 2*P.outerRadius<P.radius (0,0) := by
    by_contra! h
    exact (hball (0,0) h).2 (origin_mem_box r)
  have hwfar : 2*P.outerRadius<P.radius w := by
    by_contra! h
    exact hw (latticeBox_mono (Nat.le_succ R) (hball w h).1)
  have hsfar : 2*P.outerRadius<P.radius s := probe_far_outside _ K m d hK hm hd hscale hfar
  have hinner : 0<P.outerRadius := by
    have hi := P.inner_pos
    have hio := P.radii
    linarith
  have hends : ∀ i,P.outerRadius≤P.radius (b.endpoint i) := by
    intro i
    fin_cases i
    · change P.outerRadius≤P.radius (0,0)
      linarith
    · change P.outerRadius≤P.radius s
      linarith
    · change P.outerRadius≤P.radius w
      linarith
    · change P.outerRadius≤P.radius s
      linarith
  have hpocket : ∀ t∈dimerCell m slot c,t∈P.pocket :=
    cell_in_pocket slot z K m d hK hm hd hz hp c hc hscale
  refine ⟨v,hv,s,w,b,trim_branches P ?_ b (hpocket v hv) hpocket hsfar hends ?_⟩
  · have h := probe_mesh_margin (anchor m slot c) K m d hK hm hd hscale
    change 16*P.mesh<P.innerRadius at h
    linarith [P.mesh_pos]
  · intro t ht
    have h := probe_region_avoids_boundaries (anchor m slot c) K m d r R
      hK hm hd hscale hr hR hdr hx t ht
    exact ⟨h.2,latticeBox_mono (Nat.le_succ R) h.1⟩

#print axioms cell_pivotal_trimmed

end ExceptionalTimes.RadialBranchWitness
