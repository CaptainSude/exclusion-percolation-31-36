import ExceptionalTimes.SourceDirectSewing

/-! Exact elimination of the square-size dependence in microscopic
coefficients. Only the actual polygon cell supports need be sampled;
overwritten sites outside those supports do not affect a tested crossing. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PolygonSewing EnvironmentVariance ProbeProduct CenteredBlocks

theorem putPair_congr_on (ω η : Configuration) (S : Set Site) (heq : EqOn ω η S)
    (x z : Site) (u v : Bool) : EqOn (putPair ω x z u v) (putPair η x z u v) S := by
  intro a ha
  by_cases hax : a=x
  · subst a
    simp [putPair,Function.update_apply]
  · by_cases haz : a=x+z
    · subst a
      simp [putPair]
    · simpa only [putPair,Function.update_of_ne hax,Function.update_of_ne haz] using heq ha

theorem pairHistory_congr_on (A B : TwoTimeConfiguration) (S : Set Site)
    (heq : ∀t,EqOn (A t) (B t) S) (x z : Site) (u v : DimerBinaryResponse.State) (t : Bool) :
    EqOn (pairHistory A x z u v t) (pairHistory B x z u v t) S := by
  cases t <;> exact putPair_congr_on _ _ S (heq _) x z _ _

theorem raw_pair_local {Q : Type*} (quads : Q→PolygonQuad) (S : Finset Site)
    (hQ : ∀q,(quads q).support⊆S) (outer : (Q×Bool→Bool)→ℝ)
    (A B : TwoTimeConfiguration) (heq : ∀t,EqOn (A t) (B t) (S : Set Site))
    (rule : Rule) (x z : Site) :
    rawPairResponse rule.kernel A x z (fun ξ => outer (PolygonSewing.crossingVector quads ξ))=
      rawPairResponse rule.kernel B x z (fun ξ => outer (PolygonSewing.crossingVector quads ξ)) := by
  have hv (u v : DimerBinaryResponse.State) :
      PolygonSewing.crossingVector quads (pairHistory A x z u v)=
        PolygonSewing.crossingVector quads (pairHistory B x z u v) := by
    funext qt
    apply (quads qt.1).test_congr
    intro a ha
    exact pairHistory_congr_on A B _ heq x z u v qt.2 (hQ qt.1 ha)
  simp only [rawPairResponse,hv]

theorem averaged_pair_restrict {Q : Type*} (quads : Q→PolygonQuad) (S Λ : Finset Site)
    (hS : S⊆Λ) (hQ : ∀q,(quads q).support⊆S) (outer : (Q×Bool→Bool)→ℝ)
    (rule : Rule) (x z : Site) :
    averagedPairResponse Λ rule x z (fun ξ => outer (PolygonSewing.crossingVector quads ξ))=
      averagedPairResponse S rule x z (fun ξ => outer (PolygonSewing.crossingVector quads ξ)) := by
  apply FiniteSiteLaw.fairSites_restrict S Λ hS
    (fun ω => rawPairResponse rule.kernel (fun _ => ω) x z
      (fun ξ => outer (PolygonSewing.crossingVector quads ξ)))
  intro ω η heq
  exact raw_pair_local quads S hQ outer _ _ (fun _ _ hv => heq _ hv) rule x z

theorem averaged_multi_pair_restrict {I Q : Type*} [Fintype I]
    (quads : Q→PolygonQuad) (S Λ : Finset Site) (hS : S⊆Λ)
    (hQ : ∀q,(quads q).support⊆S) (outer : (Q×Bool→Bool)→ℝ)
    (w : I→(Bool→PairColor)→ℝ) (endpoint : I×Fin 2 ↪ Site) (rule : Rule) (x z : Site) :
    averagedMultiPairResponse Λ w rule endpoint x z (fun ξ => outer (PolygonSewing.crossingVector quads ξ))=
      averagedMultiPairResponse S w rule endpoint x z (fun ξ => outer (PolygonSewing.crossingVector quads ξ)) := by
  apply FiniteSiteLaw.fairSites_restrict S Λ hS
    (fun ω => multiPairResponse w rule.kernel (overwriteSourceHistory endpoint ω) x z
      (fun ξ => outer (PolygonSewing.crossingVector quads ξ)))
  intro ω η heq
  unfold multiPairResponse kernel
  apply Finset.sum_congr (by ext; simp)
  intro hist _
  congr 1
  exact raw_pair_local quads S hQ outer _ _
    (overwriteSourceHistory_congr endpoint ω η hist _ (fun _ hv => heq _ hv)) rule x z

noncomputable def microscopicSample {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) : Finset Site :=
  polygonFamilySupport (G.latticeQuads e he) ∪ (sourceReferenceAt e he (x 0)).support

theorem microscopicSample_subset {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) :
    microscopicSample G e he x⊆sample G e he x h := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)

theorem microscopicSample_quads {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (j : Fin q) :
    (G.latticeQuads e he j).support⊆microscopicSample G e he x := by
  intro v hv
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hv⟩)

noncomputable def microscopicTwoRuleError {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (z : Site)
    (endpoint : Fin k×Fin 2 ↪ Site) (w : Fin k→(Bool→PairColor)→ℝ)
    (r₁ r₂ : Rule) (outer : (Fin q×Bool→Bool)→ℝ) : ℝ :=
  let Λ := microscopicSample G e he x
  let F := fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)
  let J := (sourceReferenceAt e he (x 0)).jump
  averagedMultiPairResponse Λ w r₁ endpoint (x 0) z F*averagedPairResponse Λ r₂ (x 0) z J-
    averagedMultiPairResponse Λ w r₂ endpoint (x 0) z F*averagedPairResponse Λ r₁ (x 0) z J

theorem twoRuleError_eq_microscopic {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) (z : Site)
    (endpoint : Fin k×Fin 2 ↪ Site) (w : Fin k→(Bool→PairColor)→ℝ)
    (r₁ r₂ : Rule) (outer : (Fin q×Bool→Bool)→ℝ) :
    twoRuleError G e he x h z endpoint w r₁ r₂ outer=
      microscopicTwoRuleError G e he x z endpoint w r₁ r₂ outer := by
  have hm (r : Rule) := averaged_multi_pair_restrict (G.latticeQuads e he)
    (microscopicSample G e he x) (sample G e he x h) (microscopicSample_subset G e he x h)
    (microscopicSample_quads G e he x) outer w endpoint r (x 0) z
  have hs (r : Rule) := averaged_pair_restrict (fun _ : Unit => sourceReferenceAt e he (x 0))
    (microscopicSample G e he x) (sample G e he x h) (microscopicSample_subset G e he x h)
    (fun _ => Finset.subset_union_right) jumpWord r (x 0) z
  unfold twoRuleError microscopicTwoRuleError
  dsimp only
  rw [hm r₁,hm r₂]
  change averagedMultiPairResponse _ _ _ _ _ _ _*averagedPairResponse _ _ _ _
    (fun ξ => jumpWord (PolygonSewing.crossingVector (fun _ : Unit => sourceReferenceAt e he (x 0)) ξ))-
      averagedMultiPairResponse _ _ _ _ _ _ _*averagedPairResponse _ _ _ _
    (fun ξ => jumpWord (PolygonSewing.crossingVector (fun _ : Unit => sourceReferenceAt e he (x 0)) ξ))=_
  rw [hs r₁,hs r₂]
  rfl

#print axioms averaged_multi_pair_restrict
#print axioms twoRuleError_eq_microscopic
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization


