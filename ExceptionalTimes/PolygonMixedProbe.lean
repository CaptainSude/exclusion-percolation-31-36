import ExceptionalTimes.PolygonProbeProjection
import ExceptionalTimes.PolygonInteriorProbe

/-! Actual mixed bulk/half-plane probes for general axial polygon
crossings. The selected center and half-plane depend only on geometry. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

theorem polygon_mixedBoundaryArms {Q : PolygonQuad} {E : Type*}
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (A : AxialPolygonPresentation Q E) (P : Probe) {δ : ℝ}
    (he : 16*P.mesh<P.innerRadius) (hscale : 6*P.outerRadius<P.mesh*δ)
    (hparallel : ∀ i j, (A.edge i).horizontal=(A.edge j).horizontal →
      (A.edge i).level≠(A.edge j).level → δ≤|(A.edge i).level-(A.edge j).level|)
    (hroots : ∀ i,
      8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (A.edge i).first) ∧
      8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (A.edge i).last))
    (i : E) (hi : (A.edge i).contact P.mesh (HexCells.center P.center) P.outerRadius)
    (level : ℤ) (hlevel : (A.edge i).level=(level:ℝ)) :
    let q := (A.edge i).projection (HexCells.center P.center)
    ∃ H : LatticeHalfPlane, ∃ hq : q ∈ H.boundary,
      ∀ ω a b : Configuration,
        (∀ v, v ∉ P.pocket → a v=b v) → EqOn a ω P.region → EqOn b ω P.region →
        ¬ (Q.Crossing a ↔ Q.Crossing b) → MixedBoundaryArms P H q hq ω := by
  let q := (A.edge i).projection (HexCells.center P.center)
  have hR : 0<P.outerRadius := by linarith [P.radii,P.inner_pos]
  have hqseg : (A.edge i).contains q :=
    (A.edge i).projection_mem_segment P.mesh_pos.le hR hi (hroots i).1 (hroots i).2
  have hshift := polygon_projection_root_clearance A.edge (c := HexCells.center P.center)
    P.mesh_pos.le hR hroots i hi
  obtain ⟨H,_,_,hqside,hq,hcarrier,hside,hother⟩ :=
    A.local_source_geometry P q (R := P.outerRadius/8) (δ := δ)
      (by positivity) (by linarith) hparallel hshift i hqseg level hlevel
  refine ⟨H,hq,?_⟩
  intro ω a b hab ha hb hchange
  constructor
  · intro hactive
    let B := P.bulkPart q hactive
    apply polygon_fourArms_of_no_frontier hbulk Q B he _ ω a b hab
      (ha.mono (P.bulkPart_region q hactive)) (hb.mono (P.bulkPart_region q hactive)) hchange
    intro p hp
    by_contra hn
    have hpdist : dist (position P.mesh P.center) (physicalHomeomorph P p)≤
        2*min P.outerRadius (P.distanceTo q/8) := le_of_not_gt hn
    have hpfull : dist (axialPhysical P.mesh (HexCells.center P.center))
        (axialPhysical P.mesh p)≤2*P.outerRadius :=
      hpdist.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    have hline := (polygon_boundary_eq_line A.edge A.simple (c := HexCells.center P.center) P.mesh_pos.le hR hscale
      hparallel hroots i hi p hpfull).mp ((A.frontier_iff p).mp hp)
    have hd := (A.edge i).projection_distance_le_point P.mesh_pos.le
      (HexCells.center P.center) p hline
    have hd' : P.distanceTo q≤(3/2:ℝ)*dist (position P.mesh P.center) (physicalHomeomorph P p) := hd
    have hmin := min_le_right P.outerRadius (P.distanceTo q/8)
    have hact : 4*P.innerRadius<min P.outerRadius (P.distanceTo q/8) := hactive
    nlinarith [P.inner_pos]
  · intro hactive
    let HP := P.halfPart H q hq hactive
    have he' : 16*HP.mesh<HP.innerRadius := by
      change 16*P.mesh<8*max P.innerRadius (P.distanceTo q)
      have hm := le_max_left P.innerRadius (P.distanceTo q)
      linarith [P.inner_pos]
    apply hhalf Q HP (A.label i) ω a b he' hqside
    · intro p hp
      apply hcarrier p
      simpa only [HP,Probe.halfPart,HalfProbe.physical,physicalHomeomorph_apply,
        axialPhysical,dist_comm] using hp
    · intro p hp
      apply hside p
      simpa only [HP,Probe.halfPart,HalfProbe.physical,physicalHomeomorph_apply,
        axialPhysical,dist_comm] using hp
    · intro s hs p hp
      simpa only [HP,Probe.halfPart,HalfProbe.physical,physicalHomeomorph_apply,
        axialPhysical,dist_comm] using hother s hs p hp
    · intro v hv
      apply HP.changed_cell he' _ hv
      intro u hu
      exact hab u (fun hup => hu (P.halfPart_pocket H q hq hactive hup))
    · intro v hv
      have hv' := P.halfPart_region H q hq hactive (HP.cell_meets_shell he' hv)
      exact ⟨ha hv',hb hv'⟩
    · exact hchange

#print axioms polygon_mixedBoundaryArms

end ExceptionalTimes.PairSquareSewing
