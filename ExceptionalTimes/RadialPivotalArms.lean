import ExceptionalTimes.FirstBranchTrimming
import ExceptionalTimes.PlaneBranches

/-! Actual alternating four arms forced by a pivotal mesoscopic dimer cell.
The boundary and planar crossing-order inputs are explicitly identified
classical results. No local pivotal-to-arms estimate is assumed. -/

namespace ExceptionalTimes.RadialPivotalArms

open PairSquareSewing MesoscopicCells RadialFourArmProbe WiredBranches HoleFilling

theorem cell_pivotal_fourArms
    (boundaryInput : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PublishedPolygonCrossingOrder)
    {B : Type*} [Fintype B] (slot : B×Fin 2 ↪ Site) (z : Site) (K m d r R : ℕ)
    (hK : 2≤K) (hm : 0<m) (hd : d≤m) (hz : z∈latticeBox d)
    (hp : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (c : Site) (hc : c∈occupied m slot)
    (hscale : 8192*K*m≤anchorRadius m slot c)
    (hr : 0<r) (hR : 16*r≤R) (hdr : 2*d≤r)
    (hx : anchor m slot c∈annularSites (2*r-d) (R/2+d))
    (ω : Configuration)
    (hpiv : CellInterpolation.CellPivotal (wiredArmTest r R) (dimerCell m slot c) ω) :
    FourArms (probe (anchor m slot c) K m d hK hm hd hscale) ω := by
  let P := probe (anchor m slot c) K m d hK hm hd hscale
  have hscale' : 32*m≤anchorRadius m slot c := by nlinarith
  obtain ⟨v,hv,s,w,hfar,hw,⟨b⟩⟩ := PlaneBranches.dimerCell_pivotal_branches
    boundaryInput slot z m d r R hm hd hz hp (by omega) c hc hscale' ω hpiv
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
  have hends : ∀ i,P.outerRadius≤P.radius (b.toBranches.endpoint i) := by
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
  have hmesh : 2*P.mesh<P.innerRadius := by
    have h := probe_mesh_margin (anchor m slot c) K m d hK hm hd hscale
    change 16*P.mesh<P.innerRadius at h
    linarith [P.mesh_pos]
  have hregion : ∀ t∈P.region,t∉latticeBox r ∧ t∈latticeBox (R+1) := by
    intro t ht
    have h := probe_region_avoids_boundaries (anchor m slot c) K m d r R
      hK hm hd hscale hr hR hdr hx t ht
    exact ⟨h.2,latticeBox_mono (Nat.le_succ R) h.1⟩
  obtain ⟨T⟩ := trim_branches_first P hmesh b.toBranches (hpocket v hv)
    hpocket hsfar hends hregion
  apply T.fourArms_of_plane hJordan
  · have hh := hpocket v hv
    change P.radius v<P.innerRadius/2 at hh
    linarith [P.radii,P.inner_pos]
  · linarith
  · linarith
  · linarith
  · exact b.white_joined_cycle
  · simpa only [walkTrace_append,TriangularPlane.walkTrace_reverse] using b.origin_not_white
  · simpa only [walkTrace_append,TriangularPlane.walkTrace_reverse] using b.outer_not_white
  · simpa only [walkTrace_append,TriangularPlane.walkTrace_reverse]
      using b.outer_outside_origin_component

#print axioms cell_pivotal_fourArms

end ExceptionalTimes.RadialPivotalArms
