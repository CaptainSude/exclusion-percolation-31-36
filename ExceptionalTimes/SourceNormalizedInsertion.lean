import ExceptionalTimes.SourceInsertionRelabel
import ExceptionalTimes.SourceMicroscopicLimit
import ExceptionalTimes.LocalClockControl

/-! Dividing one actual insertion comparison by the local reference
responses. The reference response is a single central unit pair, not a
spatially summed pivotal jump. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CenteredBlocks ProbeProduct EnvironmentVariance

def centralS (e : ℝ) (he : 0<e) (rule : Rule) : ℝ :=
  averagedPairResponse (sourceReferenceAt e he 0).support rule 0 (1,0)
    (sourceReferenceAt e he 0).jump

theorem centralS_dyadic (n : ℕ) (rule : Rule) :
    centralS (IndependentAnnulusInput.mesh n) (IndependentAnnulusInput.mesh_pos n) rule=
      LocalDimerCalibration.localS rule n := rfl

theorem centralS_lower (B : ℝ) (hattach : UnitStaticAttachment.PublishedUnitAttachment B) :
    ∃c : ℝ,0<c ∧ ∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
      ∀hB : 0<B,∀hsmall : 4*(B*e)<1,∀rule : Rule,
        c*sourceArmCost e (B*e) he (mul_pos hB he) hsmall≤centralS e he rule := by
  obtain ⟨c,hc,e0,he0,hbound⟩ := UnitStaticAttachment.published_local_response_any_cover B hattach
  refine ⟨c,hc,e0,he0,?_⟩
  intro e he he0' hB hs rule
  exact hbound e he he0' hs 0 (by norm_num [UnitStaticAttachment.Bulk,position,triangularEmbedding])
    rule (sourceReferenceAt e he 0).support (Finset.Subset.refl _)

theorem fullCoefficient_update {k : ℕ} (Λ : Finset Site)
    (endpoint : Fin (k+1)×Fin 2 ↪ Site) (rules : Fin (k+1)→Rule)
    (i : Fin (k+1)) (rule : Rule) (x z : Site)
    (h0 : endpoint (i,0)=x) (h1 : endpoint (i,1)=x+z) (F : TwoTimeConfiguration→ℝ) :
    fullCoefficient Λ endpoint (Function.update rules i rule) F=
      averagedMultiPairResponse Λ (fun j => (rules (i.succAbove j)).insertionWeight)
        rule (residualEndpoint endpoint i) x z F := by
  rw [fullCoefficient_distinguished Λ endpoint (Function.update rules i rule) i x z h0 h1 F]
  simp only [Function.update_self,Function.update_of_ne (i.succAbove_ne _)]

def normalizedCoefficient {I : Type*} [Fintype I] (Λ : Finset Site)
    (endpoint : I×Fin 2 ↪ Site) (rules : I→Rule) (F : TwoTimeConfiguration→ℝ)
    (S : Rule→ℝ) : ℝ := fullCoefficient Λ endpoint rules F/(∏i,S (rules i))

theorem normalized_update_difference {k : ℕ} (Λ : Finset Site)
    (endpoint : Fin (k+1)×Fin 2 ↪ Site) (rules : Fin (k+1)→Rule)
    (i : Fin (k+1)) (r₁ r₂ : Rule) (F : TwoTimeConfiguration→ℝ)
    (S : Rule→ℝ) (hS : ∀r,0<S r) :
    normalizedCoefficient Λ endpoint (Function.update rules i r₁) F S-
      normalizedCoefficient Λ endpoint (Function.update rules i r₂) F S=
      (fullCoefficient Λ endpoint (Function.update rules i r₁) F*S r₂-
        fullCoefficient Λ endpoint (Function.update rules i r₂) F*S r₁)/
        (S r₁*S r₂*(∏j : Fin k,S (rules (i.succAbove j)))) := by
  unfold normalizedCoefficient
  rw [Fin.prod_univ_succAbove _ i,Fin.prod_univ_succAbove _ i]
  simp only [Function.update_self,Function.update_of_ne (i.succAbove_ne _)]
  have hprod : (∏j : Fin k,S (rules (i.succAbove j)))≠0 :=
    ne_of_gt (Finset.prod_pos (fun j _ => hS _))
  field_simp [(hS r₁).ne',(hS r₂).ne',hprod]


theorem divided_error_bound (k : ℕ) (a c K₁ K₂ S₁ S₂ D : ℝ)
    (ha : 0<a) (hc : 0<c) (hS₁ : c*a≤S₁) (hS₂ : c*a≤S₂) (hD : (c*a)^k≤D) :
    |(K₁*S₂-K₂*S₁)/(S₁*S₂*D)|≤
      (|K₁*S₂-K₂*S₁|/a^(k+2))/c^(k+2) := by
  have hca : 0<c*a := mul_pos hc ha
  have hden : 0<S₁*S₂*D := mul_pos (mul_pos (hca.trans_le hS₁) (hca.trans_le hS₂))
    ((pow_pos hca k).trans_le hD)
  have hsmall : (c*a)^(k+2)≤S₁*S₂*D := by
    calc
      _=(c*a)*(c*a)*(c*a)^k := by ring
      _≤_ := mul_le_mul (mul_le_mul hS₁ hS₂ hca.le (hca.trans_le hS₁).le) hD
        (pow_nonneg hca.le _) (mul_nonneg (hca.trans_le hS₁).le (hca.trans_le hS₂).le)
  rw [abs_div,abs_of_pos hden]
  calc
    _≤|K₁*S₂-K₂*S₁|/(c*a)^(k+2) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hca _) hsmall
    _=_ := by rw [mul_pow,div_div]; ring

theorem microscopic_error_full {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site)
    (endpoint : Fin (k+1)×Fin 2 ↪ Site)
    (h0 : ∀i,endpoint (i,0)=x i) (h1 : ∀i,endpoint (i,1)=x i+(1,0))
    (rules : Fin (k+1)→Rule) (i : Fin (k+1)) (r₁ r₂ : Rule)
    (outer : (Fin q×Bool→Bool)→ℝ) :
    microscopicTwoRuleError (G.relabel (insertionOrder i)) e he (fun j => x (insertionOrder i j))
      (1,0) (residualEndpoint endpoint i) (fun j => (rules (i.succAbove j)).insertionWeight)
      r₁ r₂ outer=
      fullCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint (Function.update rules i r₁)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))*centralS e he r₂-
      fullCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint (Function.update rules i r₂)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))*centralS e he r₁ := by
  let H := G.relabel (insertionOrder i)
  let y := fun j => x (insertionOrder i j)
  let Λ := microscopicSample H e he y
  have htest (j : Fin q) : (G.latticeQuads e he j).support⊆polygonFamilySupport (G.latticeQuads e he) :=
    fun v hv => Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hv⟩
  have hm (r : Rule) := averaged_multi_pair_restrict (G.latticeQuads e he)
    (polygonFamilySupport (G.latticeQuads e he)) Λ Finset.subset_union_left htest outer
    (fun j => (rules (i.succAbove j)).insertionWeight) (residualEndpoint endpoint i) r (x i) (1,0)
  have hs (r : Rule) := reference_pair_translation e he (x i) (1,0) r Λ
    (by
      change (sourceReferenceAt e he (x i)).support⊆polygonFamilySupport (H.latticeQuads e he) ∪
        (sourceReferenceAt e he (x i)).support
      exact Finset.subset_union_right)
  rw [fullCoefficient_update _ endpoint rules i r₁ _ _ (h0 i) (h1 i),
    fullCoefficient_update _ endpoint rules i r₂ _ _ (h0 i) (h1 i)]
  unfold microscopicTwoRuleError
  dsimp only
  simp only [insertionOrder_zero]
  change averagedMultiPairResponse Λ _ r₁ _ _ _ _*averagedPairResponse Λ r₂ _ _ _-
    averagedMultiPairResponse Λ _ r₂ _ _ _ _*averagedPairResponse Λ r₁ _ _ _=_
  rw [show (G.relabel (insertionOrder i)).latticeQuads e he=G.latticeQuads e he from rfl]
  rw [hm r₁,hm r₂,hs r₁,hs r₂]
  rfl

theorem normalized_update_bound {k : ℕ} (Λ : Finset Site)
    (endpoint : Fin (k+1)×Fin 2 ↪ Site) (rules : Fin (k+1)→Rule)
    (i : Fin (k+1)) (r₁ r₂ : Rule) (F : TwoTimeConfiguration→ℝ)
    (S : Rule→ℝ) (a c : ℝ) (ha : 0<a) (hc : 0<c) (hS : ∀r,c*a≤S r) :
    |normalizedCoefficient Λ endpoint (Function.update rules i r₁) F S-
      normalizedCoefficient Λ endpoint (Function.update rules i r₂) F S|≤
      (|fullCoefficient Λ endpoint (Function.update rules i r₁) F*S r₂-
        fullCoefficient Λ endpoint (Function.update rules i r₂) F*S r₁|/a^(k+2))/c^(k+2) := by
  rw [normalized_update_difference Λ endpoint rules i r₁ r₂ F S
    (fun r => (mul_pos hc ha).trans_le (hS r))]
  apply divided_error_bound k a c _ _ _ _ _ ha hc (hS r₁) (hS r₂)
  calc
    _ = ∏_j : Fin k,c*a := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => (mul_pos hc ha).le) (fun j _ => hS _)

theorem uniform_full_update_cross_error {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) (i : Fin (k+1)) :
    ∀δ : ℝ,0<δ→∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
      ∀x : Fin (k+1)→Site,G.Admissible e x→∀endpoint : Fin (k+1)×Fin 2 ↪ Site,
      (∀j,endpoint (j,0)=x j)→(∀j,endpoint (j,1)=x j+(1,0))→
      ∀rules : Fin (k+1)→Rule,∀r₁ r₂ : Rule,
      ∀outer : (Fin q×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→∀hB : 0<B,∀ha : 4*(B*e)<1,
      |fullCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint (Function.update rules i r₁)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))*centralS e he r₂-
      fullCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint (Function.update rules i r₂)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))*centralS e he r₁|/
        (sourceArmCost e (B*e) he (mul_pos hB he) ha)^(k+2)<δ := by
  intro δ hδ
  obtain ⟨e0,he0,hbound⟩ := uniform_microscopic_two_rule_error (G.relabel (insertionOrder i))
    B hseams hstatic hbulk hlower harmlower δ hδ
  refine ⟨e0,he0,?_⟩
  intro e he he0' x hx endpoint h0 h1 rules r₁ r₂ outer hout hB ha
  have hz : ‖triangularEmbedding ((1,0) : Site)‖≤B := by
    have ht : triangularEmbedding ((1,0) : Site)=(1 : ℂ) := by apply Complex.ext <;> norm_num [triangularEmbedding]
    rw [ht,norm_one]
    linarith [hseams.1]
  have h := hbound e he he0' (fun j => x (insertionOrder i j))
    (G.admissible_relabel (insertionOrder i) e x hx) (1,0) hz (residualEndpoint endpoint i)
    (fun j => by simpa using h0 (i.succAbove j))
    (fun j => by simpa using h1 (i.succAbove j))
    (fun j => (rules (i.succAbove j)).insertionWeight)
    (fun j => Rule.insertionWeight_centered _) (fun j => Rule.insertionWeight_variation_le_one _)
    r₁ r₂ outer hout hB ha
  rwa [microscopic_error_full G e he x endpoint h0 h1 rules i r₁ r₂ outer] at h

theorem uniform_normalized_update {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (i : Fin (k+1)) :
    ∀δ : ℝ,0<δ→∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
      ∀x : Fin (k+1)→Site,G.Admissible e x→∀endpoint : Fin (k+1)×Fin 2 ↪ Site,
      (∀j,endpoint (j,0)=x j)→(∀j,endpoint (j,1)=x j+(1,0))→
      ∀rules : Fin (k+1)→Rule,∀r₁ r₂ : Rule,
      ∀outer : (Fin q×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→
      |normalizedCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint
        (Function.update rules i r₁) (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))
        (centralS e he)-
       normalizedCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint
        (Function.update rules i r₂) (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))
        (centralS e he)|<δ := by
  intro δ hδ
  have hB : 0<B := by linarith [hseams.1]
  obtain ⟨c,hc,ec,hec,hlow⟩ := centralS_lower B hattach
  obtain ⟨ee,hee,herr⟩ := uniform_full_update_cross_error G B hseams hstatic hbulk hlower harmlower i
    (δ*c^(k+2)) (mul_pos hδ (pow_pos hc _))
  refine ⟨min ee (min ec (1/(4*B))),lt_min hee (lt_min hec (by positivity)),?_⟩
  intro e he he0 x hx endpoint h0 h1 rules r₁ r₂ outer hout
  have hee' := he0.trans_le (min_le_left _ _)
  have hec' := (he0.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hecut := (he0.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have ha : 4*(B*e)<1 := by
    have ht := (lt_div_iff₀ (show 0<4*B by positivity)).mp hecut
    nlinarith
  let a := sourceArmCost e (B*e) he (mul_pos hB he) ha
  have hapos : 0<a := sourceArmCost_pos_of_lower harmlower e he (B*e) (mul_pos hB he) ha le_rfl
  have hS (r : Rule) : c*a≤centralS e he r := hlow e he hec' hB ha r
  have hb := normalized_update_bound (polygonFamilySupport (G.latticeQuads e he)) endpoint rules i r₁ r₂
    (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)) (centralS e he) a c hapos hc hS
  have hh := herr e he hee' x hx endpoint h0 h1 rules r₁ r₂ outer hout hB ha
  have hd := (div_lt_iff₀ (pow_pos hc (k+2))).mpr hh
  exact hb.trans_lt hd

#print axioms uniform_normalized_update
#print axioms microscopic_error_full
#print axioms divided_error_bound
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization


