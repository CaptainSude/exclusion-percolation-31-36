import ExceptionalTimes.PolygonBoundarySide

/-! Actual rescaling of a fixed marked polygon and its finite boundary
presentation into lattice coordinates. No boundary vertex is discarded. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

theorem CoordinateArc.homeomorph_image {s : Set (ℝ × ℝ)} {a b : ℝ × ℝ}
    (h : CoordinateArc s a b) (e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) :
    CoordinateArc (e '' s) (e a) (e b) := by
  obtain ⟨hcompact,ha,hb,f,hf,hinj,hab,himage⟩ := h
  refine ⟨hcompact.image e.continuous,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩,
    f ∘ e.symm,hf.comp e.symm.continuous,?_,?_,?_⟩
  · rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩ hxy
    apply congrArg e
    apply hinj hu hv
    simpa only [Function.comp_apply,Homeomorph.symm_apply_apply] using hxy
  · simpa only [Function.comp_apply,Homeomorph.symm_apply_apply] using hab
  · simpa only [image_image,Function.comp_def,Homeomorph.symm_apply_apply] using himage

noncomputable def PolygonQuad.affineTransport (Q : PolygonQuad)
    (e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ))
    (hef : ∀ p, e p=f p) : PolygonQuad where
  carrier := e '' Q.carrier
  left := e '' Q.left
  right := e '' Q.right
  top := e '' Q.top
  bottom := e '' Q.bottom
  lowerLeft := e Q.lowerLeft
  upperLeft := e Q.upperLeft
  upperRight := e Q.upperRight
  lowerRight := e Q.lowerRight
  compact := Q.compact.image e.continuous
  regularClosed := by rw [← e.image_interior,← e.image_closure,Q.regularClosed]
  left_arc := Q.left_arc.homeomorph_image e
  right_arc := Q.right_arc.homeomorph_image e
  top_arc := Q.top_arc.homeomorph_image e
  bottom_arc := Q.bottom_arc.homeomorph_image e
  frontier_eq := by rw [← e.image_frontier,Q.frontier_eq]; simp only [image_union]
  polygonal := by
    rw [← e.image_frontier]
    have he : (e : (ℝ × ℝ) → (ℝ × ℝ))=f := funext hef
    rw [he]
    exact Q.polygonal.affine_image f
  left_right := (Set.disjoint_image_iff e.injective).mpr Q.left_right
  top_bottom := (Set.disjoint_image_iff e.injective).mpr Q.top_bottom
  left_top := by rw [← image_inter e.injective,Q.left_top,image_singleton]
  right_top := by rw [← image_inter e.injective,Q.right_top,image_singleton]
  left_bottom := by rw [← image_inter e.injective,Q.left_bottom,image_singleton]
  right_bottom := by rw [← image_inter e.injective,Q.right_bottom,image_singleton]

noncomputable def axialScale (c : ℝ) (hc : c≠0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Homeomorph.smulOfNeZero c hc

@[simp] theorem axialScale_apply (c : ℝ) (hc : c≠0) (p : ℝ × ℝ) :
    axialScale c hc p=c • p := rfl

noncomputable def PolygonQuad.scale (Q : PolygonQuad) (c : ℝ) (hc : c≠0) : PolygonQuad :=
  Q.affineTransport (axialScale c hc) (c • AffineMap.id ℝ (ℝ × ℝ)) (fun _ => rfl)

@[simp] theorem PolygonQuad.scale_side (Q : PolygonQuad) (c : ℝ) (hc : c≠0) (s : Bool × Bool) :
    (Q.scale c hc).side s=(axialScale c hc) '' Q.side s := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;> rfl

noncomputable def AxialSegment.scale (s : AxialSegment) (c : ℝ) (hc : c≠0) : AxialSegment where
  first := c • s.first
  last := c • s.last
  horizontal := s.horizontal
  parallel := by
    have hp := s.parallel
    cases hh : s.horizontal <;> simp only [hh,Bool.false_eq_true,ite_false,ite_true] at *
    · change c*s.first.1=c*s.last.1
      rw [hp]
    · change c*s.first.2=c*s.last.2
      rw [hp]
  nondegenerate := fun h => s.nondegenerate ((axialScale c hc).injective h)

@[simp] theorem AxialSegment.scale_point (s : AxialSegment) (c : ℝ) (hc : c≠0) (t : ℝ) :
    (s.scale c hc).point t=c • s.point t := by
  apply Prod.ext <;> simp [AxialSegment.scale,AxialSegment.point,AffineMap.lineMap_apply_module] <;> ring

theorem AxialSegment.scale_contains (s : AxialSegment) (c : ℝ) (hc : c≠0) (p : ℝ × ℝ) :
    (s.scale c hc).contains (c • p) ↔ s.contains p := by
  constructor
  · rintro ⟨t,ht,he⟩
    rw [s.scale_point] at he
    exact ⟨t,ht,(axialScale c hc).injective he⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨t,ht,s.scale_point c hc t⟩

@[simp] theorem AxialSegment.scale_level (s : AxialSegment) (c : ℝ) (hc : c≠0) :
    (s.scale c hc).level=c*s.level := by
  cases hh : s.horizontal <;> simp [AxialSegment.scale,AxialSegment.level,hh]

noncomputable def AxialPolygonPresentation.scale {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E) (c : ℝ) (hc : c≠0) :
    AxialPolygonPresentation (Q.scale c hc) E where
  edge i := (A.edge i).scale c hc
  label := A.label
  simple := by
    intro i j hij p hip hjp
    obtain ⟨q,rfl⟩ := (axialScale c hc).surjective p
    have hi := ((A.edge i).scale_contains c hc q).mp hip
    have hj := ((A.edge j).scale_contains c hc q).mp hjp
    rcases A.simple i j hij q hi hj with h | h
    · exact Or.inl (congrArg (axialScale c hc) h)
    · exact Or.inr (congrArg (axialScale c hc) h)
  side_eq := by
    intro s p
    obtain ⟨q,rfl⟩ := (axialScale c hc).surjective p
    rw [PolygonQuad.scale_side]
    have hm : (axialScale c hc) q ∈ (axialScale c hc) '' Q.side s ↔ q ∈ Q.side s := by
      constructor
      · rintro ⟨p,hp,he⟩
        exact (axialScale c hc).injective he ▸ hp
      · intro hq
        exact ⟨q,hq,rfl⟩
    rw [hm,A.side_eq]
    simp only [axialScale_apply,AxialSegment.scale_contains]

/-- A dyadic physical level is an integer level after passage to any
finer compatible dyadic mesh. -/
theorem dyadic_level_integer (k n : ℕ) (hkn : k≤n) (z : ℤ) :
    ∃ m : ℤ, (2:ℝ)^n*((z:ℝ)/(2:ℝ)^k)=(m:ℝ) := by
  refine ⟨(2:ℤ)^(n-k)*z,?_⟩
  have hp : (2:ℝ)^n=(2:ℝ)^(n-k)*(2:ℝ)^k := by
    rw [← pow_add,Nat.sub_add_cancel hkn]
  rw [hp]
  push_cast
  field_simp

theorem AxialPolygonPresentation.dyadic_scale_integer {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E) (k n : ℕ) (hkn : k≤n)
    (hlevels : ∀ i, ∃ z : ℤ, (A.edge i).level=(z:ℝ)/(2:ℝ)^k) :
    ∀ i, ∃ m : ℤ, ((A.scale ((2:ℝ)^n) (pow_ne_zero _ (by norm_num))).edge i).level=(m:ℝ) := by
  intro i
  obtain ⟨z,hz⟩ := hlevels i
  change ∃ m : ℤ, ((A.edge i).scale ((2:ℝ)^n) (pow_ne_zero _ (by norm_num))).level=(m:ℝ)
  rw [AxialSegment.scale_level,hz]
  exact dyadic_level_integer k n hkn z

theorem physicalHomeomorph_inverse_scale (P : Probe) (p : ℝ × ℝ) :
    physicalHomeomorph P (P.mesh⁻¹ • p)=axialPlaneHomeomorph p := by
  have hm := ne_of_gt P.mesh_pos
  apply Complex.ext <;>
    simp [physicalHomeomorph_apply,axialPlaneHomeomorph,HexTiling.planeMap,Complex.mul_re,
      Complex.mul_im,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;>
    field_simp

/-- The physical marked carrier stays fixed when its lattice-coordinate
presentation is divided by the mesh. -/
theorem PolygonQuad.physical_scaled_carrier (Q : PolygonQuad) (P : Probe) :
    physicalHomeomorph P '' (Q.scale P.mesh⁻¹ (inv_ne_zero (ne_of_gt P.mesh_pos))).carrier=
      axialPlaneHomeomorph '' Q.carrier := by
  change physicalHomeomorph P '' (axialScale P.mesh⁻¹ _ '' Q.carrier)=_
  rw [image_image]
  congr 1
  funext p
  exact physicalHomeomorph_inverse_scale P p

theorem PolygonQuad.physical_scaled_side (Q : PolygonQuad) (P : Probe) (s : Bool × Bool) :
    physicalHomeomorph P '' (Q.scale P.mesh⁻¹ (inv_ne_zero (ne_of_gt P.mesh_pos))).side s=
      axialPlaneHomeomorph '' Q.side s := by
  rw [Q.scale_side,image_image]
  congr 1
  funext p
  exact physicalHomeomorph_inverse_scale P p

#print axioms PolygonQuad.scale
#print axioms AxialPolygonPresentation.scale
#print axioms AxialPolygonPresentation.dyadic_scale_integer

end ExceptionalTimes.PairSquareSewing
