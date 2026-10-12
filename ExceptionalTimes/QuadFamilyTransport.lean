import ExceptionalTimes.PolygonLocalChange

/-! The actual change of planar grid used for quad approximation. The
boundary-reparametrization witnesses are retained. A dense/countable
family stays dense/countable under the fixed Euclidean-to-axial shear.
This proves the change of grid; it does not assume a percolation estimate. -/

open Set
open scoped Classical unitInterval
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

abbrev QuadSquare := I × I

def quadCorner (b : Bool × Bool) : QuadSquare :=
  (if b.1 then 1 else 0, if b.2 then 1 else 0)

def quadSquareBoundary : Set QuadSquare :=
  {p | p.1=0 ∨ p.1=1 ∨ p.2=0 ∨ p.2=1}

/-- A homeomorphic image of the compact square, with its four marked
corners retained by the parametrization. -/
structure ParameterQuad (X : Type*) [TopologicalSpace X] where
  map : QuadSquare → X
  continuous : Continuous map
  injective : Function.Injective map

namespace ParameterQuad

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[ext] theorem ext {Q R : ParameterQuad X} (h : Q.map=R.map) : Q=R := by
  cases Q
  cases R
  cases h
  rfl

noncomputable def transport (e : X ≃ₜ Y) (Q : ParameterQuad X) : ParameterQuad Y where
  map := e ∘ Q.map
  continuous := e.continuous.comp Q.continuous
  injective := e.injective.comp Q.injective

@[simp] theorem transport_apply (e : X ≃ₜ Y) (Q : ParameterQuad X) (p : QuadSquare) :
    (Q.transport e).map p=e (Q.map p) := rfl

@[simp] theorem transport_symm (e : X ≃ₜ Y) (Q : ParameterQuad Y) :
    (Q.transport e.symm).transport e=Q := by
  ext p
  exact e.apply_symm_apply _

theorem isClosedEmbedding [T2Space X] (Q : ParameterQuad X) :
    Topology.IsClosedEmbedding Q.map := Q.continuous.isClosedEmbedding Q.injective

end ParameterQuad

def BoundaryApprox {X : Type*} [PseudoMetricSpace X]
    (Q R : ParameterQuad X) (ε : ℝ) : Prop :=
  ∃ φ : QuadSquare ≃ₜ QuadSquare,
    (∀ b, φ (quadCorner b)=quadCorner b) ∧
    ∀ p ∈ quadSquareBoundary, dist (Q.map p) (R.map (φ p))<ε

/-- Density formulated with the literal witnesses for the quad metric's
infimum over corner-preserving boundary reparametrizations. -/
def BoundaryDense {X : Type*} [PseudoMetricSpace X]
    (D : Set X) (family : Set (ParameterQuad X)) : Prop :=
  ∀ Q : ParameterQuad X, range Q.map ⊆ D → ∀ ε : ℝ, 0<ε →
    ∃ R ∈ family, BoundaryApprox Q R ε

theorem BoundaryApprox.transport {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : X ≃ₜ Y) {C ε : ℝ} (hC : 0<C)
    (hL : ∀ x y, dist (e x) (e y)≤C*dist x y)
    {Q R : ParameterQuad X} (h : BoundaryApprox Q R ε) :
    BoundaryApprox (Q.transport e) (R.transport e) (C*ε) := by
  obtain ⟨φ,hφ,hclose⟩ := h
  refine ⟨φ,hφ,fun p hp => ?_⟩
  exact (hL _ _).trans_lt (mul_lt_mul_of_pos_left (hclose p hp) hC)

theorem BoundaryDense.transport {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : X ≃ₜ Y) {C : ℝ} (hC : 0<C)
    (hL : ∀ x y, dist (e x) (e y)≤C*dist x y)
    {D : Set X} {family : Set (ParameterQuad X)} (h : BoundaryDense D family) :
    BoundaryDense (e '' D) ((fun Q => Q.transport e) '' family) := by
  intro Q hQ ε hε
  have hQD : range (Q.transport e.symm).map ⊆ D := by
    rintro x ⟨p,rfl⟩
    obtain ⟨y,hy,he⟩ := hQ ⟨p,rfl⟩
    change e.symm (Q.map p) ∈ D
    rw [← he,e.symm_apply_apply]
    exact hy
  obtain ⟨R,hR,hclose⟩ := h (Q.transport e.symm) hQD (ε/C) (div_pos hε hC)
  refine ⟨R.transport e,⟨R,hR,rfl⟩,?_⟩
  have ht := hclose.transport e hC hL
  simpa only [ParameterQuad.transport_symm,mul_div_cancel₀ ε hC.ne'] using ht

theorem countable_transported_quad_family {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {family : Set (ParameterQuad X)} (h : family.Countable) :
    ((fun Q => Q.transport e) '' family).Countable := h.image _

noncomputable def euclideanAxialShear : ℂ ≃ₜ ℂ :=
  Complex.equivRealProdCLM.toHomeomorph.trans axialPlaneHomeomorph

theorem euclideanAxialShear_apply (z : ℂ) :
    euclideanAxialShear z=HexTiling.planeMap (z.re,z.im) := rfl

theorem euclideanAxialShear_dist (z w : ℂ) :
    dist (euclideanAxialShear z) (euclideanAxialShear w)≤2*dist z w := by
  rw [euclideanAxialShear_apply,euclideanAxialShear_apply,dist_eq_norm,
    ← HexTiling.planeMap_sub,dist_eq_norm]
  have h := HexTiling.planeMap_norm_le_coordinates ((z.re,z.im)-(w.re,w.im))
  have hre := Complex.abs_re_le_norm (z-w)
  have him := Complex.abs_im_le_norm (z-w)
  simp only [Prod.fst_sub,Prod.snd_sub,Complex.sub_re,Complex.sub_im] at *
  linarith

/-- Any literal dense Euclidean quad family gives a dense family on the
axial grid after the fixed shear. In particular this applies to the
published dyadic family once its parametrizations are supplied. -/
theorem axial_quad_family_dense {D : Set ℂ} {family : Set (ParameterQuad ℂ)}
    (h : BoundaryDense D family) :
    BoundaryDense (euclideanAxialShear '' D)
      ((fun Q => Q.transport euclideanAxialShear) '' family) :=
  h.transport euclideanAxialShear (by norm_num) euclideanAxialShear_dist

#print axioms BoundaryDense.transport
#print axioms axial_quad_family_dense

end ExceptionalTimes.PairSquareSewing
