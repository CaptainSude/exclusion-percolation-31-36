import ExceptionalTimes.PolygonCrossingLocality
import ExceptionalTimes.PolygonLocalHalfPlane

/-! A changed literal polygon crossing selects the inside component when
the probe misses the boundary. Thus its actual full ball is a bulk probe. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

theorem polygon_bulk_ball_of_no_frontier (Q : PolygonQuad) (P : Probe)
    (he : 16*P.mesh<P.innerRadius) {a b : Configuration}
    (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (hchange : ¬ (Q.Crossing a ↔ Q.Crossing b))
    (havoid : ∀ p ∈ frontier Q.carrier,
      2*P.outerRadius<dist (position P.mesh P.center) (physicalHomeomorph P p)) :
    Metric.closedBall (position P.mesh P.center) (2*P.outerRadius) ⊆
      physicalHomeomorph P '' interior Q.carrier := by
  let S : Set (ℝ × ℝ) := physicalHomeomorph P ⁻¹'
    Metric.closedBall (position P.mesh P.center) (2*P.outerRadius)
  have hconv : Convex ℝ S :=
    (convex_closedBall (position P.mesh P.center) (2*P.outerRadius)).linear_preimage
      (axialPhysicalLinear P.mesh)
  have hn : ∀ p ∈ S, p ∉ frontier Q.carrier := by
    intro p hp hf
    exact not_lt_of_ge (by simpa only [S,mem_preimage,Metric.mem_closedBall,dist_comm] using hp)
      (havoid p hf)
  have hs : S ⊆ interior Q.carrier := by
    rcases preconnected_avoiding_frontier Q.compact.isClosed hconv.isPreconnected hn with hi | ho
    · exact hi
    · obtain ⟨z,⟨p,hp,rfl⟩,hz⟩ := Q.changed_carrier_meets_buffered_ball P he hab hchange
      have hpS : p ∈ S := by
        change dist (physicalHomeomorph P p) (position P.mesh P.center)≤2*P.outerRadius
        have hd : dist (physicalHomeomorph P p) (position P.mesh P.center)<3*P.innerRadius/4 := hz
        linarith [P.radii,P.inner_pos]
      exact False.elim (ho hpS hp)
  intro z hz
  refine ⟨(physicalHomeomorph P).symm z,hs ?_,(physicalHomeomorph P).apply_symm_apply z⟩
  change physicalHomeomorph P ((physicalHomeomorph P).symm z) ∈
    Metric.closedBall (position P.mesh P.center) (2*P.outerRadius)
  simpa only [Homeomorph.apply_symm_apply] using hz

theorem polygon_fourArms_of_no_frontier (hsource : PublishedPolygonBulkArms)
    (Q : PolygonQuad) (P : Probe) (he : 16*P.mesh<P.innerRadius)
    (havoid : ∀ p ∈ frontier Q.carrier,
      2*P.outerRadius<dist (position P.mesh P.center) (physicalHomeomorph P p))
    (ω a b : Configuration) (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (ha : EqOn a ω P.region) (hb : EqOn b ω P.region)
    (hchange : ¬ (Q.Crossing a ↔ Q.Crossing b)) : FourArms P ω := by
  apply hsource Q P ω a b he (polygon_bulk_ball_of_no_frontier Q P he hab hchange havoid)
  · exact fun v hv => changed_cell_in_buffered_ball P he hab hv
  · exact fun v hv => ⟨ha (cell_meets_agreementShell_in_region P he hv),
      hb (cell_meets_agreementShell_in_region P he hv)⟩
  · simpa only [Q.physicalCrossing_iff] using hchange

/-- The no-contact condition concerns the actual finite polygon segments,
not their supporting lines or an unrelated bounding rectangle. -/
theorem polygon_fourArms_of_no_contact {E : Type*} (hsource : PublishedPolygonBulkArms)
    (Q : PolygonQuad) (P : Probe) (edge : E → AxialSegment)
    (hboundary : ∀ p, p ∈ frontier Q.carrier ↔ ∃ i, (edge i).contains p)
    (he : 16*P.mesh<P.innerRadius)
    (hcontact : ∀ i, ¬ (edge i).contact P.mesh (HexCells.center P.center) P.outerRadius)
    (ω a b : Configuration) (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (ha : EqOn a ω P.region) (hb : EqOn b ω P.region)
    (hchange : ¬ (Q.Crossing a ↔ Q.Crossing b)) : FourArms P ω := by
  apply polygon_fourArms_of_no_frontier hsource Q P he _ ω a b hab ha hb hchange
  intro p hp
  by_contra hn
  obtain ⟨i,t,ht,hp'⟩ := (hboundary p).mp hp
  apply hcontact i
  refine ⟨t,ht,?_⟩
  rw [hp']
  exact le_of_not_gt hn

#print axioms polygon_bulk_ball_of_no_frontier
#print axioms polygon_fourArms_of_no_contact

end ExceptionalTimes.PairSquareSewing
