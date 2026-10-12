import ExceptionalTimes.GridQuadPresentation
import ExceptionalTimes.PolygonScaling

/-! Narrow geometric published input.

Garban, Pete and Schramm, Pivotal, cluster and interface measures for
critical planar percolation, Definition 2.1 and its following paragraph:
https://arxiv.org/html/1008.1378v5#S2.SS2

The dyadic quads in a bounded domain form a countable dense family. Their
boundaries consist of dyadic grid edges, and their four marked points are
dyadic vertices. We choose one square parametrization per geometric quad;
we do not assert that the set of all parametrizations is countable.
Density is written using the literal corner-preserving witnesses in the
metric of Section 2.2. No arm or percolation probability is an input here.
The side labels and polygon fields are derived from the unlabeled edges.
-/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

noncomputable def dyadicNormalization (k : ℕ) : ℂ ≃ₜ (ℝ × ℝ) :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    (axialScale ((2:ℝ)^k) (pow_ne_zero _ (by norm_num)))

/-- The literal dyadic geometry of one parametrized quad. -/
structure DyadicGridQuad (Q : ParameterQuad ℂ) where
  level : ℕ
  level_pos : 1≤level
  grid : ParameterUnitBoundary (Q.transport (dyadicNormalization level))

def PublishedDyadicQuadDensity : Prop :=
  ∀ D : Set ℂ, IsOpen D → Bornology.IsBounded D →
    ∃ family : Set (ParameterQuad ℂ), family.Countable ∧ BoundaryDense D family ∧
      ∀ Q ∈ family, range Q.map ⊆ D ∧ Nonempty (DyadicGridQuad Q)

theorem published_axial_quad_family (hsource : PublishedDyadicQuadDensity)
    (D : Set ℂ) (hopen : IsOpen D) (hbounded : Bornology.IsBounded D) :
    ∃ family : Set (ParameterQuad ℂ), family.Countable ∧
      BoundaryDense (euclideanAxialShear '' D) family ∧
      ∀ Q ∈ family, ∃ R : ParameterQuad ℂ, Nonempty (DyadicGridQuad R) ∧
        range R.map ⊆ D ∧ Q=R.transport euclideanAxialShear := by
  obtain ⟨family,hcount,hdense,hgrid⟩ := hsource D hopen hbounded
  refine ⟨(fun Q => Q.transport euclideanAxialShear) '' family,
    countable_transported_quad_family euclideanAxialShear hcount,
    axial_quad_family_dense hdense,?_⟩
  rintro Q ⟨R,hR,rfl⟩
  exact ⟨R,(hgrid R hR).2,(hgrid R hR).1,rfl⟩

namespace DyadicGridQuad

variable {Q : ParameterQuad ℂ} (A : DyadicGridQuad Q)

noncomputable def polygon (hsource : PublishedInvarianceOfDomain) : PolygonQuad :=
  (A.grid.presentation.polygonQuad hsource).scale ((2:ℝ)^A.level)⁻¹
    (inv_ne_zero (pow_ne_zero _ (by norm_num)))

noncomputable def presentation (hsource : PublishedInvarianceOfDomain) :
    AxialPolygonPresentation (A.polygon hsource) A.grid.edges :=
  (A.grid.presentation.presentation hsource).scale ((2:ℝ)^A.level)⁻¹
    (inv_ne_zero (pow_ne_zero _ (by norm_num)))

theorem presentation_dyadic (hsource : PublishedInvarianceOfDomain) (e : A.grid.edges) :
    ∃ z : ℤ, ((A.presentation hsource).edge e).level=(z:ℝ)/(2:ℝ)^A.level := by
  obtain ⟨z,hz⟩ := A.grid.presentation_integer e
  refine ⟨z,?_⟩
  change ((A.grid.presentation.edge e).scale ((2:ℝ)^A.level)⁻¹
    (inv_ne_zero (pow_ne_zero _ (by norm_num)))).level=_
  rw [AxialSegment.scale_level,hz]
  ring

theorem polygon_carrier (hsource : PublishedInvarianceOfDomain) :
    (A.polygon hsource).carrier=
      range (Q.transport Complex.equivRealProdCLM.toHomeomorph).map := by
  change (axialScale ((2:ℝ)^A.level)⁻¹ _) ''
    range (Q.transport (dyadicNormalization A.level)).map=_
  rw [← range_comp]
  congr 1
  funext p
  change ((2:ℝ)^A.level)⁻¹ • ((2:ℝ)^A.level •
    Complex.equivRealProdCLM.toHomeomorph (Q.map p))=_
  rw [smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)),one_smul]
  rfl

theorem polygon_side (hsource : PublishedInvarianceOfDomain) (s : Bool × Bool) :
    (A.polygon hsource).side s=
      (Q.transport Complex.equivRealProdCLM.toHomeomorph).map '' squareSide s := by
  change ((A.grid.presentation.polygonQuad hsource).scale ((2:ℝ)^A.level)⁻¹ _).side s=_
  rw [PolygonQuad.scale_side,A.grid.presentation.polygonQuad_side]
  rw [image_image]
  congr 1
  funext p
  change ((2:ℝ)^A.level)⁻¹ • ((2:ℝ)^A.level •
    Complex.equivRealProdCLM.toHomeomorph (Q.map p))=_
  rw [smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)),one_smul]
  rfl

theorem physical_carrier (hsource : PublishedInvarianceOfDomain) :
    axialPlaneHomeomorph '' (A.polygon hsource).carrier=
      range (Q.transport euclideanAxialShear).map := by
  rw [A.polygon_carrier,← range_comp]
  rfl

theorem physical_side (hsource : PublishedInvarianceOfDomain) (s : Bool × Bool) :
    axialPlaneHomeomorph '' (A.polygon hsource).side s=
      (Q.transport euclideanAxialShear).map '' squareSide s := by
  rw [A.polygon_side,image_image]
  rfl

/-- The same original edge set is retained at every finer mesh. In
particular, no extra roots are inserted at microscopic collinear vertices. -/
noncomputable def meshPolygon (hsource : PublishedInvarianceOfDomain) (n : ℕ) : PolygonQuad :=
  (A.polygon hsource).scale ((2:ℝ)^n) (pow_ne_zero _ (by norm_num))

noncomputable def meshPresentation (hsource : PublishedInvarianceOfDomain) (n : ℕ) :
    AxialPolygonPresentation (A.meshPolygon hsource n) A.grid.edges :=
  (A.presentation hsource).scale ((2:ℝ)^n) (pow_ne_zero _ (by norm_num))

theorem meshPresentation_integer (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (hn : A.level≤n) (e : A.grid.edges) :
    ∃ z : ℤ, ((A.meshPresentation hsource n).edge e).level=(z:ℝ) :=
  (A.presentation hsource).dyadic_scale_integer A.level n hn (A.presentation_dyadic hsource) e

theorem mesh_connectedCrossing_iff (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (hn : A.level≤n) (ω : Configuration) :
    (A.meshPolygon hsource n).ConnectedCrossing ω ↔
      (A.meshPolygon hsource n).Crossing ω :=
  (A.meshPresentation hsource n).connectedCrossing_iff
    (A.meshPresentation_integer hsource n hn) ω

#print axioms mesh_connectedCrossing_iff

end DyadicGridQuad
end ExceptionalTimes.PairSquareSewing

