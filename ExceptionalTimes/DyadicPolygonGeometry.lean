import ExceptionalTimes.DyadicCrossingDictionary

/-! The polygon forest's feature spacing and fixed roots for a literal
dyadic quad. They follow from integer coordinates of the original coarse
edges, uniformly at every finer mesh. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing
namespace DyadicGridQuad

variable {Q : ParameterQuad ℂ} (A : DyadicGridQuad Q)

noncomputable def meshSpacing (n : ℕ) : ℝ := (2:ℝ)^n/(2:ℝ)^A.level

theorem meshSpacing_pos (n : ℕ) : 0<A.meshSpacing n := by
  unfold meshSpacing
  positivity

theorem mesh_level_multiple (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (e : A.grid.edges) :
    ∃ z : ℤ, ((A.meshPresentation hsource n).edge e).level=A.meshSpacing n*(z:ℝ) := by
  obtain ⟨z,hz⟩ := A.presentation_dyadic hsource e
  refine ⟨z,?_⟩
  change (((A.presentation hsource).edge e).scale ((2:ℝ)^n)
    (pow_ne_zero _ (by norm_num))).level=_
  rw [AxialSegment.scale_level,hz]
  unfold meshSpacing
  ring

theorem mesh_level_separation (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (e f : A.grid.edges)
    (hne : ((A.meshPresentation hsource n).edge e).level≠
      ((A.meshPresentation hsource n).edge f).level) :
    A.meshSpacing n≤|((A.meshPresentation hsource n).edge e).level-
      ((A.meshPresentation hsource n).edge f).level| := by
  obtain ⟨z,hz⟩ := A.mesh_level_multiple hsource n e
  obtain ⟨w,hw⟩ := A.mesh_level_multiple hsource n f
  have hzw : z-w≠0 := by
    intro he
    have he' : z=w := sub_eq_zero.mp he
    apply hne
    rw [hz,hw,he']
  have hone : (1:ℝ)≤|((z-w:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs hzw
  rw [hz,hw,← mul_sub,abs_mul,abs_of_pos (A.meshSpacing_pos n)]
  have hcast : (z:ℝ)-(w:ℝ)=((z-w:ℤ):ℝ) := by push_cast; rfl
  rw [hcast]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (A.meshSpacing_pos n).le

theorem physical_spacing (n : ℕ) :
    ((2:ℝ)^n)⁻¹*A.meshSpacing n=((2:ℝ)^A.level)⁻¹ := by
  unfold meshSpacing
  field_simp

theorem forest_scale_condition (n : ℕ) (ε stop : ℝ)
    (hmesh : ε=((2:ℝ)^n)⁻¹)
    (hstop : 6*(stop/8)<((2:ℝ)^A.level)⁻¹) :
    6*(stop/8)<ε*A.meshSpacing n := by
  rw [hmesh,A.physical_spacing]
  exact hstop

theorem mesh_endpoint (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (P : Probe) (hmesh : P.mesh=((2:ℝ)^n)⁻¹)
    (e : A.grid.edges) (b : Bool) :
    axialPhysical P.mesh (if b then ((A.meshPresentation hsource n).edge e).last
      else ((A.meshPresentation hsource n).edge e).first)=
    axialPlaneHomeomorph (if b then ((A.presentation hsource).edge e).last
      else ((A.presentation hsource).edge e).first) := by
  cases b
  · change physicalHomeomorph P ((2:ℝ)^n • ((A.presentation hsource).edge e).first)=_
    simpa [hmesh] using
      physicalHomeomorph_inverse_scale P ((A.presentation hsource).edge e).first
  · change physicalHomeomorph P ((2:ℝ)^n • ((A.presentation hsource).edge e).last)=_
    simpa [hmesh] using
      physicalHomeomorph_inverse_scale P ((A.presentation hsource).edge e).last

#print axioms mesh_level_separation
#print axioms mesh_endpoint

end DyadicGridQuad
end ExceptionalTimes.PairSquareSewing
