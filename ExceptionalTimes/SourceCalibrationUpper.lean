import ExceptionalTimes.SourceFixedArmComparison

/-! Ordinary upper bounds for the actual microscopic reference response.
The same fixed64 static probe is used for both canonical and refresh rules. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PolygonSewing EnvironmentVariance ProbeProduct

theorem averaged_pair_bound_of_arms {Q : Type*} (quads : Q→PolygonQuad)
    (outer : (Q×Bool→Bool)→ℝ) (hbound : ∀c,|outer c|≤1)
    (P : Probe) (z : Site) (rule : Rule) (Λ : Finset Site)
    (hlocal : ∀q,PolygonSewing.LocalChangeArms (quads q) P)
    (hpair : P.center∈P.pocket ∧ P.center+z∈P.pocket) :
    |averagedPairResponse Λ rule P.center z (fun ξ => outer (PolygonSewing.crossingVector quads ξ))|≤
      2*probability (sourceLaw Λ) (fun ω => FourArms P (complete ω.1)) := by
  let F := fun ξ => outer (PolygonSewing.crossingVector quads ξ)
  let f := fun ω : ↥Λ→Bool => rawPairResponse rule.kernel (fun _ => complete ω) P.center z F
  have hdensity : ∀ω,|f ω|≤2*indicator (FourArms P (complete ω)) := by
    apply abs_le_indicator_of_support f (fun ω => FourArms P (complete ω)) 2
    · exact fun _ => rawPairResponse_bound rule.kernel _ _ _ _ (fun _ => hbound _)
    · intro ω hne
      exact PolygonSewing.pair_response_source_arm quads outer rule.kernel P z (complete ω)
        (fun _ => complete ω) hlocal hpair (fun _ _ _ => rfl) hne
  rw [source_probability_first]
  change |(fairSites Λ).expect f|≤2*probability (fairSites Λ) (fun ω => FourArms P (complete ω))
  calc
    _≤(fairSites Λ).expect (fun ω => |f ω|) := FiniteLaw.abs_expect_le _ _
    _≤(fairSites Λ).expect (fun ω => 2*indicator (FourArms P (complete ω))) :=
      FiniteLaw.expect_mono _ hdensity
    _=_ := FiniteLaw.expect_const_mul _ _ _

/-- The pair calibrator upper constant depends on the fixed physical
geometry and B, not on the sewing tolerance, M or h. -/
theorem reference_pair_upper {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hstatic : PublishedFixedRadiusFourArmComparison B) (hbulk : PublishedPolygonBulkArms) :
    ∃C : ℝ,0<C ∧ ∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
      ∀h : ℝ,∀x : Fin (k+1)→Site,∀z : Site,‖triangularEmbedding z‖≤B→
      ∀hB : 0<B,∀_hsmall : 4*(64*(B*e))<outerRadius G,∀ha : 4*(B*e)<1,
      ∀rule : Rule,∀outer : (Unit×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→
      |averagedPairResponse (sample G e he x h) rule (x 0) z
        (fun ξ => outer (PolygonSewing.crossingVector (fun _ : Unit => sourceReferenceAt e he (x 0)) ξ))|≤
      C*sourceArmCost e (B*e) he (mul_pos hB he) ha := by
  obtain ⟨C,hC,e0,he0,hbound⟩ := hstatic.2 (outerRadius G) (outerRadius_pos G)
    (by linarith [outerRadius_le G])
  refine ⟨2*C,mul_pos (by norm_num) hC,e0,he0,?_⟩
  intro e he he0' h x z hz hB hsmall ha rule outer hout
  let P := fixedOtherProbe G e he B hB hsmall (x 0)
  have hinner : 16*e<P.innerRadius := by
    change 16*e<64*(B*e)
    nlinarith [hstatic.1]
  have hpair : P.center∈P.pocket ∧ P.center+z∈P.pocket := by
    apply pair_fits_pocket P
    change |e| * ‖triangularEmbedding z‖<64*(B*e)/2
    rw [abs_of_pos he]
    nlinarith [mul_pos hB he]
  have hp := averaged_pair_bound_of_arms (fun _ : Unit => sourceReferenceAt e he (x 0)) outer hout
    P z rule (sample G e he x h)
    (fun _ => source_reference_localChange G hbulk e he (x 0) P rfl rfl rfl hinner) hpair
  have hcover : sourceDiskSites P.mesh P.mesh_pos P.center (2*P.outerRadius)⊆sample G e he x h := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (G.disk_sites_subset e he x _ 0 hv))
  rw [source_probe_probability_disk P _ hcover] at hp
  have hb := hbound e he he0' (x 0) hB hsmall ha
  exact hp.trans (by simpa only [P,fixedOtherProbe,microProbe,mul_assoc] using mul_le_mul_of_nonneg_left hb (show (0 : ℝ)≤2 by norm_num))

#print axioms averaged_pair_bound_of_arms
#print axioms reference_pair_upper
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization




