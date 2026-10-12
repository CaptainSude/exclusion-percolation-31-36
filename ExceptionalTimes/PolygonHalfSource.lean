import ExceptionalTimes.PolygonBoundarySide
import ExceptionalTimes.PolygonCrossingLocality

/-! Literal published boundary necessity specialized using the proved
finite polygon geometry, retaining all true vertices and marked points. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

def PolygonLocalChangeHalfArms (Q : PolygonQuad) (P : HalfProbe) : Prop :=
  ∀ ω a b : Configuration,
    (∀ v, v ∉ P.pocket → a v=b v) → EqOn a ω P.region → EqOn b ω P.region →
    ¬ (Q.Crossing a ↔ Q.Crossing b) → HalfThreeArms P ω

/-- The half-plane and its orientation are derived from the polygon
carrier. The assumptions describe actual finite segments, clearance from
every endpoint, and the published one-probe local-change result. -/
theorem polygon_halfProbe_from_published {Q : PolygonQuad} {E : Type*}
    (hsource : PublishedPolygonHalfArms) (A : AxialPolygonPresentation Q E)
    (P : Probe) (c : ℝ × ℝ) {r R δ : ℝ}
    (hr : 0<r) (hrR : 4*r<R) (he : 16*P.mesh<r) (hscale : 6*R<P.mesh*δ)
    (hparallel : ∀ i j, (A.edge i).horizontal=(A.edge j).horizontal →
      (A.edge i).level≠(A.edge j).level → δ≤|(A.edge i).level-(A.edge j).level|)
    (hroots : ∀ i,
      8*R≤dist (axialPhysical P.mesh c) (axialPhysical P.mesh (A.edge i).first) ∧
      8*R≤dist (axialPhysical P.mesh c) (axialPhysical P.mesh (A.edge i).last))
    (i : E) (hc : (A.edge i).contains c)
    (level : ℤ) (hlevel : (A.edge i).level=(level:ℝ)) :
    ∃ H : HalfProbe,
      H.mesh=P.mesh ∧ H.center=c ∧ H.innerRadius=r ∧ H.outerRadius=R ∧
      H.halfPlane.horizontal=(A.edge i).horizontal ∧ H.halfPlane.level=level ∧
      PolygonLocalChangeHalfArms Q H := by
  have hR : 0<R := by linarith
  obtain ⟨H,hhor,hlvl,hcside,hcline,hcarrier,hside,hother⟩ :=
    A.local_source_geometry P c hR hscale hparallel hroots i hc level hlevel
  let HP : HalfProbe := {
    mesh := P.mesh
    halfPlane := H
    center := c
    center_on_line := hcline
    innerRadius := r
    outerRadius := R
    mesh_pos := P.mesh_pos
    inner_pos := hr
    radii := hrR }
  refine ⟨HP,rfl,rfl,rfl,rfl,hhor,hlvl,?_⟩
  intro ω a b hab ha hb hchange
  apply hsource Q HP (A.label i) ω a b he hcside
  · intro p hp
    apply hcarrier p
    simpa only [HP,HalfProbe.physical,physicalHomeomorph_apply,axialPhysical,dist_comm] using hp
  · intro p hp
    apply hside p
    simpa only [HP,HalfProbe.physical,physicalHomeomorph_apply,axialPhysical,dist_comm] using hp
  · intro s hs p hp
    simpa only [HP,HalfProbe.physical,physicalHomeomorph_apply,axialPhysical,dist_comm]
      using hother s hs p hp
  · exact fun v hv => HP.changed_cell he hab hv
  · exact fun v hv => ⟨ha (HP.cell_meets_shell he hv),hb (HP.cell_meets_shell he hv)⟩
  · exact hchange

#print axioms polygon_halfProbe_from_published

end ExceptionalTimes.PairSquareSewing
