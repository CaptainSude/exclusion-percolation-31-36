import ExceptionalTimes.SourceCalibrationUpper

/-! Exact fair-law enlargement of the reference square calibrator, and
the ordinary source02 lower-power input for the literal circular cuts. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PolygonSewing EnvironmentVariance ProbeProduct

theorem square_jump_response_restrict (Q : PolygonQuad) (D S Λ : Finset Site)
    (hS : S⊆Λ) (hQ : Q.support⊆S) :
    averagedSquareResponse Λ D Q.jump=averagedSquareResponse S D Q.jump := by
  apply FiniteSiteLaw.fairSites_restrict S Λ hS
    (fun ω => rawSquareResponse D (fun _ => ω) Q.jump)
  intro ω η hagree
  have ht (b : Bool) : Q.test (force D ω b)=Q.test (force D η b) := by
    apply Q.test_congr
    intro v hv
    by_cases hvD : v∈D
    · simp [force,hvD]
    · simpa only [force,ite_eq_right hvD] using hagree v (hQ hv)
  rw [PolygonSewing.square_jump_half_pivotal,PolygonSewing.square_jump_half_pivotal,ht true,ht false]

theorem referenceSample_subset_sample {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) :
    referenceSample e he (x 0) h⊆sample G e he x h := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  · exact Finset.mem_union_right _ hv

theorem reference_square_jump_lower_sample (hsource : PublishedReferenceSquareLower) :
    ∃c : ℝ,0<c ∧ ∃h0 : ℝ,0<h0 ∧ ∀h : ℝ,∀hh : 0<h,h<h0→
      ∃hb : 4*h<1,∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
        ∀q k (G : SourceSeparatedGeometry q k) (x : Fin (k+1)→Site),
        c*sourceArmCost e h he hh hb≤
          averagedSquareResponse (sample G e he x h) (sourceSquareSites e he (x 0) h)
            (sourceReferenceAt e he (x 0)).jump := by
  obtain ⟨c,hc,h0,hh0,hbound⟩ := reference_square_jump_lower hsource
  refine ⟨c,hc,h0,hh0,?_⟩
  intro h hh hh0'
  obtain ⟨hb,e0,he0,hbnd⟩ := hbound h hh hh0'
  refine ⟨hb,e0,he0,?_⟩
  intro e he he0' q k G x
  rw [square_jump_response_restrict _ _ (referenceSample e he (x 0) h) _
    (referenceSample_subset_sample G e he x h) (Finset.subset_union_left)]
  exact hbnd e he he0' (x 0)

/-- Named ordinary static consequence of source02 Lemma2.1 lower four-arm
power bound and its explicitly allowed fixed-shape/circular-cut margins.
B is the fixed sufficiently large microscopic cutoff. No dynamical or
pair assertion is part of this input. -/
def PublishedCircularArmLower (B : ℝ) : Prop :=
  128≤B ∧ ∃c : ℝ,0<c ∧ ∃g : ℝ,0<g ∧
    ∀e : ℝ,∀he : 0<e,∀r : ℝ,∀hr : 0<r,∀hsmall : 4*r<1,
      B*e≤r→c*r^g≤sourceArmCost e r he hr hsmall

theorem sourceArmCost_pos_of_lower {B : ℝ} (hsource : PublishedCircularArmLower B)
    (e : ℝ) (he : 0<e) (r : ℝ) (hr : 0<r) (hsmall : 4*r<1) (hcut : B*e≤r) :
    0<sourceArmCost e r he hr hsmall := by
  obtain ⟨_,c,hc,g,_hg,hbound⟩ := hsource
  exact (mul_pos hc (Real.rpow_pos_of_pos hr g)).trans_le (hbound e he r hr hsmall hcut)

#print axioms square_jump_response_restrict
#print axioms reference_square_jump_lower_sample
#print axioms sourceArmCost_pos_of_lower
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization

