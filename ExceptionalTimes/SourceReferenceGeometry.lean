import ExceptionalTimes.SourceFiniteGeometry
import ExceptionalTimes.StraightBoxPolygon

/-! The literal source06 calibration rectangle Q0, rather than an
arbitrary reference area. Its physical image is [-1,1] by [-1/2,1/2],
with the vertical sides as terminals. All constructions are geometric.
-/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing
noncomputable section

def referencePullback (p : ℝ×ℝ) : ℝ×ℝ :=
  (p.1-p.2/(2*Real.sqrt 3),p.2/Real.sqrt 3)

noncomputable def referencePullbackHomeomorph : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) where
  toFun := referencePullback
  invFun := fun p => (p.1+p.2/2,Real.sqrt 3*p.2)
  left_inv p := by
    have hs : Real.sqrt (3:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    apply Prod.ext
    all_goals simp [referencePullback]
    all_goals field_simp
    all_goals ring
  right_inv p := by
    have hs : Real.sqrt (3:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    apply Prod.ext
    all_goals simp [referencePullback]
    all_goals field_simp
    all_goals ring
  continuous_toFun := by unfold referencePullback; fun_prop
  continuous_invFun := by fun_prop

noncomputable def referencePullbackLinear : (ℝ×ℝ) →ₗ[ℝ] (ℝ×ℝ) where
  toFun := referencePullback
  map_add' p q := by apply Prod.ext <;> simp [referencePullback] <;> ring
  map_smul' c p := by apply Prod.ext <;> simp [referencePullback] <;> ring

noncomputable def sourceReferenceQuad : PolygonQuad :=
  (straightBoxPolygonQuad 1 (by decide)).affineTransport referencePullbackHomeomorph
    referencePullbackLinear.toAffineMap (fun _ => rfl)

theorem planeMap_referencePullback (p : ℝ×ℝ) :
    HexTiling.planeMap (referencePullback p) = ⟨p.1,p.2/2⟩ := by
  have hs : Real.sqrt (3:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply Complex.ext
  all_goals simp [HexTiling.planeMap,referencePullback]
  all_goals field_simp
  all_goals ring

theorem sourceReferenceQuad_carrier :
    HexTiling.planeMap '' sourceReferenceQuad.carrier =
      {z : ℂ | z.re ∈ Icc (-1) 1 ∧ z.im ∈ Icc (-1/2) (1/2)} := by
  change HexTiling.planeMap '' (referencePullbackHomeomorph '' axialRectangle 1) = _
  rw [image_image]
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    change (HexTiling.planeMap (referencePullback p)).re ∈ _ ∧
      (HexTiling.planeMap (referencePullback p)).im ∈ _
    rw [planeMap_referencePullback]
    have hp' : p.1∈Icc (-1) 1 ∧ p.2∈Icc (-1) 1 := by simpa only [axialRectangle,Nat.cast_one] using Set.mem_prod.mp hp
    exact ⟨hp'.1,by dsimp; constructor <;> linarith [hp'.2.1,hp'.2.2]⟩
  · intro hz
    refine ⟨(z.re,2*z.im),?_,?_⟩
    ·
      apply Set.mem_prod.mpr
      norm_num only [Nat.cast_one,Prod.fst,Prod.snd]
      exact ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
    · change HexTiling.planeMap (referencePullback (z.re,2*z.im))=z
      rw [planeMap_referencePullback]
      apply Complex.ext <;> simp

theorem sourceReferenceQuad_left :
    HexTiling.planeMap '' sourceReferenceQuad.left =
      {z : ℂ | z.re = -1 ∧ z.im ∈ Icc (-1/2) (1/2)} := by
  change HexTiling.planeMap '' (referencePullbackHomeomorph '' straightLeft 1) = _
  rw [image_image]
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    change (HexTiling.planeMap (referencePullback p)).re = _ ∧
      (HexTiling.planeMap (referencePullback p)).im ∈ _
    rw [planeMap_referencePullback]
    have hp' : p.1 = -1 ∧ p.2∈Icc (-1) 1 := by simpa [straightLeft] using hp
    exact ⟨hp'.1,by dsimp; constructor <;> linarith [hp'.2.1,hp'.2.2]⟩
  · intro hz
    refine ⟨(z.re,2*z.im),?_,?_⟩
    ·
      simp only [straightLeft,Set.mem_ofPred_eq,Nat.cast_one,Set.mem_Icc]
      exact ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
    · change HexTiling.planeMap (referencePullback (z.re,2*z.im))=z
      rw [planeMap_referencePullback]
      apply Complex.ext <;> simp

theorem sourceReferenceQuad_right :
    HexTiling.planeMap '' sourceReferenceQuad.right =
      {z : ℂ | z.re = 1 ∧ z.im ∈ Icc (-1/2) (1/2)} := by
  change HexTiling.planeMap '' (referencePullbackHomeomorph '' straightRight 1) = _
  rw [image_image]
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    change (HexTiling.planeMap (referencePullback p)).re = _ ∧
      (HexTiling.planeMap (referencePullback p)).im ∈ _
    rw [planeMap_referencePullback]
    have hp' : p.1 = 1 ∧ p.2∈Icc (-1) 1 := by simpa [straightRight] using hp
    exact ⟨hp'.1,by dsimp; constructor <;> linarith [hp'.2.1,hp'.2.2]⟩
  · intro hz
    refine ⟨(z.re,2*z.im),?_,?_⟩
    ·
      simp only [straightRight,Set.mem_ofPred_eq,Nat.cast_one,Set.mem_Icc]
      exact ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
    · change HexTiling.planeMap (referencePullback (z.re,2*z.im))=z
      rw [planeMap_referencePullback]
      apply Complex.ext <;> simp

noncomputable def PolygonQuad.shift (Q : PolygonQuad) (v : ℝ×ℝ) : PolygonQuad :=
  Q.affineTransport (Homeomorph.addLeft v)
    (AffineMap.const ℝ (ℝ×ℝ) v + AffineMap.id ℝ (ℝ×ℝ)) (fun _ => rfl)

noncomputable def sourceReferenceAt (e : ℝ) (he : 0<e) (x : Site) : PolygonQuad :=
  (sourceReferenceQuad.scale e⁻¹ (inv_ne_zero he.ne')).shift (HexCells.center x)

theorem sourcePhysicalMap_shift_scale (e : ℝ) (he : 0<e) (x : Site) (p : ℝ×ℝ) :
    sourcePhysicalMap e he (HexCells.center x + e⁻¹ • p) =
      position e x + HexTiling.planeMap p := by
  change (e : ℂ) * HexTiling.planeMap (HexCells.center x + e⁻¹ • p) = _
  rw [← sourcePhysicalMap_center e he x]
  change (e : ℂ) * HexTiling.planeMap (HexCells.center x + e⁻¹ • p) =
    (e : ℂ) * HexTiling.planeMap (HexCells.center x) + HexTiling.planeMap p
  apply Complex.ext
  all_goals simp [HexTiling.planeMap,Complex.mul_re,Complex.mul_im]
  all_goals field_simp
  all_goals ring

theorem sourcePhysicalMap_shift_scale_image (e : ℝ) (he : 0<e) (x : Site)
    (S : Set (ℝ×ℝ)) :
    sourcePhysicalMap e he ''
      (Homeomorph.addLeft (HexCells.center x) '' (axialScale e⁻¹ (inv_ne_zero he.ne') '' S)) =
    (fun z : ℂ => position e x + z) '' (HexTiling.planeMap '' S) := by
  simp only [image_image]
  congr 1
  funext p
  exact sourcePhysicalMap_shift_scale e he x p

theorem sourceReferenceAt_carrier (e : ℝ) (he : 0<e) (x : Site) :
    sourcePhysicalMap e he '' (sourceReferenceAt e he x).carrier =
      (fun z : ℂ => position e x + z) ''
        {z : ℂ | z.re ∈ Icc (-1) 1 ∧ z.im ∈ Icc (-1/2) (1/2)} := by
  change sourcePhysicalMap e he ''
    (Homeomorph.addLeft (HexCells.center x) ''
      (axialScale e⁻¹ (inv_ne_zero he.ne') '' sourceReferenceQuad.carrier)) = _
  rw [sourcePhysicalMap_shift_scale_image,sourceReferenceQuad_carrier]

theorem sourceReferenceAt_left (e : ℝ) (he : 0<e) (x : Site) :
    sourcePhysicalMap e he '' (sourceReferenceAt e he x).left =
      (fun z : ℂ => position e x + z) ''
        {z : ℂ | z.re = -1 ∧ z.im ∈ Icc (-1/2) (1/2)} := by
  change sourcePhysicalMap e he ''
    (Homeomorph.addLeft (HexCells.center x) ''
      (axialScale e⁻¹ (inv_ne_zero he.ne') '' sourceReferenceQuad.left)) = _
  rw [sourcePhysicalMap_shift_scale_image,sourceReferenceQuad_left]

theorem sourceReferenceAt_right (e : ℝ) (he : 0<e) (x : Site) :
    sourcePhysicalMap e he '' (sourceReferenceAt e he x).right =
      (fun z : ℂ => position e x + z) ''
        {z : ℂ | z.re = 1 ∧ z.im ∈ Icc (-1/2) (1/2)} := by
  change sourcePhysicalMap e he ''
    (Homeomorph.addLeft (HexCells.center x) ''
      (axialScale e⁻¹ (inv_ne_zero he.ne') '' sourceReferenceQuad.right)) = _
  rw [sourcePhysicalMap_shift_scale_image,sourceReferenceQuad_right]

#print axioms sourceReferenceAt_carrier
#print axioms sourceReferenceAt_left
#print axioms sourceReferenceAt_right
#print axioms sourceReferenceQuad_carrier
#print axioms sourceReferenceQuad_left
#print axioms sourceReferenceQuad_right

end
end ExceptionalTimes.PairSquareSewing




