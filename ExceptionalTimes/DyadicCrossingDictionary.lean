import ExceptionalTimes.DyadicQuadInput

/-! Exact crossing convention under the change of planar coordinates.
The physical dyadic quad is fixed while its lattice-coordinate polygon
is refined, and the black set is the actual union of closed hexagons. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

def ClosedCrossingSets {X : Type*} [TopologicalSpace X]
    (black carrier left right : Set X) : Prop :=
  ∃ K : Set X, IsClosed K ∧ IsConnected K ∧ K ⊆ black ∩ carrier ∧
    (K ∩ left).Nonempty ∧ (K ∩ right).Nonempty

theorem ClosedCrossingSets.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {black carrier left right : Set X}
    (h : ClosedCrossingSets black carrier left right) :
    ClosedCrossingSets (e '' black) (e '' carrier) (e '' left) (e '' right) := by
  obtain ⟨K,hclosed,hconnected,hsub,hleft,hright⟩ := h
  refine ⟨e '' K,e.isClosedMap K hclosed,hconnected.image e e.continuous.continuousOn,?_,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact ⟨⟨x,(hsub hx).1,rfl⟩,⟨x,(hsub hx).2,rfl⟩⟩
  · obtain ⟨x,hx,hxl⟩ := hleft
    exact ⟨e x,⟨x,hx,rfl⟩,⟨x,hxl,rfl⟩⟩
  · obtain ⟨x,hx,hxr⟩ := hright
    exact ⟨e x,⟨x,hx,rfl⟩,⟨x,hxr,rfl⟩⟩

theorem closedCrossingSets_image_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (black carrier left right : Set X) :
    ClosedCrossingSets (e '' black) (e '' carrier) (e '' left) (e '' right) ↔
      ClosedCrossingSets black carrier left right := by
  constructor
  · intro h
    simpa only [image_image,Function.comp_def,Homeomorph.symm_apply_apply,image_id'] using
      h.image e.symm
  · exact fun h => h.image e

def ParameterQuad.LiteralCrossing {X : Type*} [TopologicalSpace X]
    (Q : ParameterQuad X) (black : Set X) : Prop :=
  ClosedCrossingSets black (range Q.map)
    (Q.map '' squareSide (false,false)) (Q.map '' squareSide (false,true))

theorem ParameterQuad.literalCrossing_transport {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (Q : ParameterQuad X)
    (e : X ≃ₜ Y) (black : Set X) :
    (Q.transport e).LiteralCrossing (e '' black) ↔ Q.LiteralCrossing black := by
  change ClosedCrossingSets (e '' black) (range (e ∘ Q.map))
    ((e ∘ Q.map) '' squareSide (false,false))
    ((e ∘ Q.map) '' squareSide (false,true)) ↔ _
  rw [range_comp]
  simpa only [image_image,ParameterQuad.LiteralCrossing,Function.comp_def] using
    closedCrossingSets_image_iff e black (range Q.map)
      (Q.map '' squareSide (false,false)) (Q.map '' squareSide (false,true))

theorem ParameterQuad.literalCrossing_eq (Q : ParameterQuad (ℝ × ℝ))
    (black : Set (ℝ × ℝ)) : Q.LiteralCrossing black ↔ Q.ClosedCrossing black := Iff.rfl

namespace DyadicGridQuad

variable {Q : ParameterQuad ℂ} (A : DyadicGridQuad Q)

theorem mesh_physical_carrier (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (P : Probe) (hmesh : P.mesh=((2:ℝ)^n)⁻¹) :
    physicalHomeomorph P '' (A.meshPolygon hsource n).carrier=
      range (Q.transport euclideanAxialShear).map := by
  calc
    _ = axialPlaneHomeomorph '' (A.polygon hsource).carrier := by
      simpa only [hmesh,inv_inv,meshPolygon] using (A.polygon hsource).physical_scaled_carrier P
    _ = _ := A.physical_carrier hsource

theorem mesh_physical_side (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (P : Probe) (hmesh : P.mesh=((2:ℝ)^n)⁻¹) (s : Bool × Bool) :
    physicalHomeomorph P '' (A.meshPolygon hsource n).side s=
      (Q.transport euclideanAxialShear).map '' squareSide s := by
  calc
    _ = axialPlaneHomeomorph '' (A.polygon hsource).side s := by
      simpa only [hmesh,inv_inv,meshPolygon] using (A.polygon hsource).physical_scaled_side P s
    _ = _ := A.physical_side hsource s

/-- The literal closed-set crossing of the same fixed physical quad is
exactly the finite-polygon path crossing consumed by the forest estimate. -/
theorem physical_crossing_dictionary (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (hn : A.level≤n) (P : Probe) (hmesh : P.mesh=((2:ℝ)^n)⁻¹)
    (ω : Configuration) :
    (Q.transport euclideanAxialShear).LiteralCrossing (globalPhysicalBlackCells P ω) ↔
      (A.meshPolygon hsource n).Crossing ω := by
  rw [ParameterQuad.LiteralCrossing,physicalBlackCells_eq_image,
    ← A.mesh_physical_carrier hsource n P hmesh,
    ← A.mesh_physical_side hsource n P hmesh (false,false),
    ← A.mesh_physical_side hsource n P hmesh (false,true),
    closedCrossingSets_image_iff]
  exact A.mesh_connectedCrossing_iff hsource n hn ω

#print axioms physical_crossing_dictionary

end DyadicGridQuad
end ExceptionalTimes.PairSquareSewing
