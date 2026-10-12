import ExceptionalTimes.SourcePolygonTranslation

/-! Exact translated calibrator identity under the ordinary finite fair
law. Every finite cover is allowed, and auxiliary sample colors are summed out. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PolygonSewing EnvironmentVariance ProbeProduct FiniteHaar

theorem fair_expect_pullback_shift (S Λ : Finset Site) (x : Site)
    (hcover : ∀v∈S,x+v∈Λ) (F : Configuration→ℝ)
    (hlocal : ∀ω η,(∀v∈S,ω v=η v)→F ω=F η) :
    (fairSites Λ).expect (fun ω => F (fun v => complete ω (x+v)))=
      (fairSites S).expect (fun ω => F (complete ω)) := by
  let slot : ↥Λ ↪ Site := ⟨fun v => v.val-x,by
    intro v w h
    apply Subtype.ext
    exact sub_left_injective h⟩
  have hslot : ∀v∈S,∃a,slot a=v := by
    intro v hv
    exact ⟨⟨x+v,hcover v hv⟩,by simp [slot]⟩
  have hdict := FiniteSiteLaw.average_site_embedding slot S hslot F hlocal
  rw [FiniteSiteLaw.fairSites_expect_eq_average]
  change average (fun ω : ↥Λ→Bool => F (Function.extend slot ω (fun _ => false)))=
    (fairSites S).expect (fun ω => F (complete ω)) at hdict
  rw [←hdict]
  apply congrArg average
  funext ω
  apply hlocal
  intro v hv
  have hm := hcover v hv
  have hse : slot ⟨x+v,hm⟩=v := by simp [slot]
  rw [←hse,slot.injective.extend_apply]
  simp [slot,complete,hm]

theorem averaged_pair_jump_shift (Q : PolygonQuad) (x y z : Site) (rule : Rule)
    (Λ : Finset Site) (hcover : (Q.shift (HexCells.center x)).support⊆Λ) :
    averagedPairResponse Λ rule (x+y) z (Q.shift (HexCells.center x)).jump=
      averagedPairResponse Q.support rule y z Q.jump := by
  unfold averagedPairResponse
  have hr : (fun ω : ↥Λ→Bool => rawPairResponse rule.kernel (fun _ => complete ω) (x+y) z
      (Q.shift (HexCells.center x)).jump)=
      fun ω => rawPairResponse rule.kernel (fun _ a => complete ω (x+a)) y z Q.jump := by
    funext ω
    exact raw_pair_jump_shift Q x y z (complete ω) rule
  rw [hr]
  apply fair_expect_pullback_shift Q.support Λ x
    (fun v hv => hcover ((support_shift Q x v).mpr hv))
    (fun ω => rawPairResponse rule.kernel (fun _ => ω) y z Q.jump)
  intro ω η heq
  exact raw_pair_local (fun _ : Unit => Q) Q.support (fun _ => Finset.Subset.refl _)
    jumpWord (fun _ => ω) (fun _ => η) (fun _ _ hv => heq _ hv) rule y z

/-- Local microscopic calibration is independent of its lattice center.
Both sides are actual Q0 jump responses; this does not identify either
side with a globally summed reference jump. -/
theorem reference_pair_translation (e : ℝ) (he : 0<e) (x z : Site) (rule : Rule)
    (Λ : Finset Site) (hcover : (sourceReferenceAt e he x).support⊆Λ) :
    averagedPairResponse Λ rule x z (sourceReferenceAt e he x).jump=
      averagedPairResponse (sourceReferenceAt e he 0).support rule 0 z
        (sourceReferenceAt e he 0).jump := by
  let Q := sourceReferenceQuad.scale e⁻¹ (inv_ne_zero he.ne')
  have hx := averaged_pair_jump_shift Q x 0 z rule Λ hcover
  have h0 := averaged_pair_jump_shift Q 0 0 z rule (sourceReferenceAt e he 0).support
    (Finset.Subset.refl _)
  simpa only [Q,sourceReferenceAt,add_zero] using hx.trans h0.symm

#print axioms fair_expect_pullback_shift
#print axioms reference_pair_translation
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization

