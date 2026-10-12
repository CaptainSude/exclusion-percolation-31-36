import ExceptionalTimes.SourceUniformSewing
import ExceptionalTimes.SourceCalibrationSampling

/-! Direct comparison of the two actual microscopic rules through one
common fixed square. The square response cancels algebraically. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PolygonSewing EnvironmentVariance CenteredBlocks

noncomputable def jumpWord (c : Unit×Bool→Bool) : ℝ :=
  if c ((),false)≠c ((),true) then 1 else 0

theorem jumpWord_bound (c : Unit×Bool→Bool) : |jumpWord c|≤1 := by
  unfold jumpWord
  split <;> norm_num

noncomputable def twoRuleError {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) (z : Site)
    (endpoint : Fin k×Fin 2 ↪ Site) (w : Fin k→(Bool→PairColor)→ℝ)
    (r₁ r₂ : Rule) (outer : (Fin q×Bool→Bool)→ℝ) : ℝ :=
  let Λ := sample G e he x h
  let F := fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)
  let J := (sourceReferenceAt e he (x 0)).jump
  averagedMultiPairResponse Λ w r₁ endpoint (x 0) z F*averagedPairResponse Λ r₂ (x 0) z J-
    averagedMultiPairResponse Λ w r₂ endpoint (x 0) z F*averagedPairResponse Λ r₁ (x 0) z J

theorem actual_two_rule_bound {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) (z : Site)
    (endpoint : Fin k×Fin 2 ↪ Site) (w : Fin k→(Bool→PairColor)→ℝ)
    (r₁ r₂ : Rule) (outer : (Fin q×Bool→Bool)→ℝ)
    (a b c C δ : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hC : 0≤C)
    (hD : c*b≤averagedSquareResponse (sample G e he x h) (sourceSquareSites e he (x 0) h)
      (sourceReferenceAt e he (x 0)).jump)
    (hS₁ : |averagedPairResponse (sample G e he x h) r₁ (x 0) z (sourceReferenceAt e he (x 0)).jump|≤C*a)
    (hS₂ : |averagedPairResponse (sample G e he x h) r₂ (x 0) z (sourceReferenceAt e he (x 0)).jump|≤C*a)
    (hE₁ : |fullSquareError G e he x h z endpoint w r₁ outer jumpWord|/(a^(k+1)*b)≤δ)
    (hE₂ : |fullSquareError G e he x h z endpoint w r₂ outer jumpWord|/(a^(k+1)*b)≤δ) :
    |twoRuleError G e he x h z endpoint w r₁ r₂ outer|/a^(k+2)≤2*(C/c)*δ := by
  have hbnd := CommonSquare.normalized_abs_bound (k+1) ha hb hc hD hS₁ hS₂
    (K₁ := averagedMultiPairResponse (sample G e he x h) w r₁ endpoint (x 0) z
      (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)))
    (K₂ := averagedMultiPairResponse (sample G e he x h) w r₂ endpoint (x 0) z
      (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)))
    (H := averagedMultiSquareResponse (sample G e he x h) w endpoint (sourceSquareSites e he (x 0) h)
      (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)))
  change |twoRuleError G e he x h z endpoint w r₁ r₂ outer|/a^(k+2)≤
    (C/c)*((|fullSquareError G e he x h z endpoint w r₁ outer jumpWord|+
      |fullSquareError G e he x h z endpoint w r₂ outer jumpWord|)/(a^(k+1)*b)) at hbnd
  rw [add_div] at hbnd
  have he := mul_le_mul_of_nonneg_left (add_le_add hE₁ hE₂) (div_nonneg hC hc.le)
  exact hbnd.trans (he.trans_eq (by ring))

/-- Uniform normalized two-rule comparison on the concrete finite sample.
No equality of microscopic amplitudes and no two-microscopic-arm sewing
hypothesis is used. The remaining h-dependence of the finite sample can
be removed by the separately checked iid locality dictionary. -/
theorem uniform_two_rule_error {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) :
    ∀δ : ℝ,0<δ→∃h0 : ℝ,0<h0 ∧ ∀h : ℝ,∀_hh : 0<h,h<h0→
      ∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
        ∀x : Fin (k+1)→Site,G.Admissible e x→∀z : Site,‖triangularEmbedding z‖≤B→
        ∀endpoint : Fin k×Fin 2 ↪ Site,
        (∀i,endpoint (i,0)=x i.succ)→(∀i,endpoint (i,1)=x i.succ+z)→
        ∀w : Fin k→(Bool→PairColor)→ℝ,(∀i,∑a,w i a=0)→(∀i,variation (w i)≤1)→
        ∀r₁ r₂ : Rule,∀outer : (Fin q×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→
        ∀hB : 0<B,∀ha : 4*(B*e)<1,
        |twoRuleError G e he x h z endpoint w r₁ r₂ outer|/
          (sourceArmCost e (B*e) he (mul_pos hB he) ha)^(k+2)<δ := by
  obtain ⟨C,hC,eu,heu,hupper⟩ := reference_pair_upper G B hstatic hbulk
  obtain ⟨c,hc,hd,hhd,hD⟩ := reference_square_jump_lower_sample hlower
  intro δ hδ
  let t := δ/(4*(C/c+1))
  have hratio : 0<C/c := div_pos hC hc
  have ht : 0<t := div_pos hδ (by positivity)
  obtain ⟨hs,hhs,hE⟩ := uniform_full_square_error G B hseams hstatic hbulk t ht
  refine ⟨min hs hd,lt_min hhs hhd,?_⟩
  intro h hh hh0
  obtain ⟨es,hes,hEs⟩ := hE h hh (hh0.trans_le (min_le_left _ _))
  obtain ⟨hb,ed,hed,hDs⟩ := hD h hh (hh0.trans_le (min_le_right _ _))
  have hBpos : 0<B := by linarith [hseams.1]
  let em := min es (min ed (min eu (min (h/(2*B)) (outerRadius G/(512*B)))))
  have hem : 0<em := by
    dsimp [em]
    exact lt_min hes (lt_min hed (lt_min heu (lt_min (by positivity)
      (div_pos (outerRadius_pos G) (by positivity)))))
  refine ⟨em,hem,?_⟩
  intro e he he0 x hx z hz endpoint hfirst hsecond w hw hvar r₁ r₂ outer hout hB ha
  have hes' := he0.trans_le (min_le_left _ _)
  have hed' := he0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heu' := he0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heh : e<h/(2*B) := he0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have heR : e<outerRadius G/(512*B) := he0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hcut : B*e≤h := by
    have hh' := (lt_div_iff₀ (show 0<2*B by positivity)).mp heh
    nlinarith
  have hsmall : 4*(64*(B*e))<outerRadius G := by
    have hr' := (lt_div_iff₀ (show 0<512*B by positivity)).mp heR
    nlinarith [mul_pos hB he]
  have hapos := sourceArmCost_pos_of_lower harmlower e he (B*e) (mul_pos hB he) ha le_rfl
  have hbpos := sourceArmCost_pos_of_lower harmlower e he h hh hb hcut
  have hS₁ := hupper e he heu' h x z hz hB hsmall ha r₁ jumpWord jumpWord_bound
  have hS₂ := hupper e he heu' h x z hz hB hsmall ha r₂ jumpWord jumpWord_bound
  have hE₁ := hEs e he hes' x hx z hz endpoint hfirst hsecond w r₁ hw hvar outer jumpWord hout jumpWord_bound hB ha hb
  have hE₂ := hEs e he hes' x hx z hz endpoint hfirst hsecond w r₂ hw hvar outer jumpWord hout jumpWord_bound hB ha hb
  have hresult := actual_two_rule_bound G e he x h z endpoint w r₁ r₂ outer _ _ c C t
    hapos hbpos hc hC.le (hDs e he hed' q k G x) hS₁ hS₂ hE₁ hE₂
  apply hresult.trans_lt
  have hteq : t*(4*(C/c+1))=δ := div_mul_cancel₀ δ (by positivity)
  nlinarith

#print axioms actual_two_rule_bound
#print axioms uniform_two_rule_error
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization

