import ExceptionalTimes.SourceFixedArmComparison

/-! Uniform full centered sewing on a compact separated insertion range.
The static comparison constant is chosen before the requested error;
source M and its finite trials are then fixed before h, and h before e. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
open PolygonSewing EnvironmentVariance CenteredBlocks

noncomputable def fullSquareError {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) (z : Site)
    (endpoint : Fin k×Fin 2 ↪ Site) (w : Fin k→(Bool→PairColor)→ℝ) (rule : Rule)
    (outerA : (Fin q×Bool→Bool)→ℝ) (outerB : (Unit×Bool→Bool)→ℝ) : ℝ :=
  let Λ := sample G e he x h
  let D := sourceSquareSites e he (x 0) h
  let F := fun ξ => outerA (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)
  let H := fun ξ => outerB (PolygonSewing.crossingVector (fun _ : Unit => sourceReferenceAt e he (x 0)) ξ)
  CommonSquare.squareError (averagedMultiPairResponse Λ w rule endpoint (x 0) z F)
    (averagedPairResponse Λ rule (x 0) z H) (averagedMultiSquareResponse Λ w endpoint D F)
    (averagedSquareResponse Λ D H)

/-- The normalization also handles zero static costs, without silently
assuming an arm-positivity theorem. -/
theorem normalized_full_bound {k : ℕ} (err ε a b C : ℝ)
    (hε : 0≤ε) (ha : 0≤a) (hb : 0≤b) (hC : 0≤C)
    (w : Fin k→(Bool→PairColor)→ℝ) (hvar : ∀i,variation (w i)≤1)
    (cost : Fin k→ℝ) (hcost0 : ∀i,0≤cost i) (hcost : ∀i,cost i≤C*a)
    (herr : |err|≤4*(∏i,variation (w i))*ε*(a*b)*(∏i,cost i)) :
    |err|/(a^(k+1)*b)≤4*ε*C^k := by
  have hV0 : 0≤∏i,variation (w i) := Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hV1 : (∏i,variation (w i))≤1 := by
    simpa only [variation,Finset.prod_const_one] using Finset.prod_le_prod₀
      (fun i (_ : i∈(Finset.univ : Finset (Fin k))) => Finset.sum_nonneg (fun _ _ => abs_nonneg (w i _)))
      (fun i _ => hvar i)
  have hP0 : 0≤∏i,cost i := Finset.prod_nonneg (fun i _ => hcost0 i)
  have hP : (∏i,cost i)≤∏_i : Fin k,C*a := Finset.prod_le_prod₀ (fun i _ => hcost0 i) (fun i _ => hcost i)
  have hraw : |err|≤4*1*ε*(a*b)*(∏_i : Fin k,C*a) := herr.trans (by gcongr)
  by_cases ha0 : a=0
  · simp only [ha0,zero_pow (Nat.succ_ne_zero k),zero_mul,div_zero]
    positivity
  by_cases hb0 : b=0
  · simp only [hb0,mul_zero,div_zero]
    positivity
  simpa only [Fintype.card_fin,mul_one] using source_full_normalization (I := Fin k)
    err 1 ε a b C (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)) hraw

/-- Actual source trials imply the full fixed-degree relative error,
uniformly over all literal pair placements in the chosen compact range.
The order is tolerance, fixed trials, square radius h, mesh e. -/
theorem uniform_full_square_error {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) :
    ∀δ : ℝ,0<δ→∃h0 : ℝ,0<h0 ∧ ∀h : ℝ,∀hh : 0<h,h<h0→
      ∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
        ∀x : Fin (k+1)→Site,G.Admissible e x→∀z : Site,‖triangularEmbedding z‖≤B→
        ∀endpoint : Fin k×Fin 2 ↪ Site,
        (∀i,endpoint (i,0)=x i.succ)→(∀i,endpoint (i,1)=x i.succ+z)→
        ∀w : Fin k→(Bool→PairColor)→ℝ,∀rule : Rule,
        (∀i,∑a,w i a=0)→(∀i,variation (w i)≤1)→
        ∀outerA : (Fin q×Bool→Bool)→ℝ,∀outerB : (Unit×Bool→Bool)→ℝ,
        (∀c,|outerA c|≤1)→(∀c,|outerB c|≤1)→
        ∀hB : 0<B,∀ha : 4*(B*e)<1,∀hb : 4*h<1,
        |fullSquareError G e he x h z endpoint w rule outerA outerB|/
          ((sourceArmCost e (B*e) he (mul_pos hB he) ha)^(k+1)*sourceArmCost e h he hh hb)≤δ := by
  obtain ⟨C,hC,ec,hec,hcost⟩ := fixed_other_arm_bound G B hstatic
  intro δ hδ
  let ε := δ/(8*C^k)
  have hε : 0<ε := div_pos hδ (mul_pos (by norm_num) (pow_pos hC k))
  obtain ⟨M,hM,n,_hn,L,hL,radii,hr,houter,hsep,h0,hh0,htrials⟩ := hseams.2 q k G ε hε
  refine ⟨h0,hh0,?_⟩
  intro h hh hh0'
  obtain ⟨et,het,ht⟩ := htrials h hh hh0'
  refine ⟨min et (min ec (h/4)),lt_min het (lt_min hec (by positivity)),?_⟩
  intro e he he0 x hx z hz endpoint hfirst hsecond w rule hw hvar outerA outerB hboundA hboundB hB ha hb
  have het' := he0.trans_le (min_le_left _ _)
  have hec' := he0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hesmall := he0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hB',hM',hr',hL',hmic,hsq,ha',hb',hbuffer,⟨T⟩⟩ := ht e he het' x hx
  have hraw := T.full_centered_bound hbulk hseams.1 hM hx hesmall houter hsep hbuffer z hz
    endpoint hfirst hsecond w rule hw outerA outerB hboundA hboundB
  dsimp only at hraw
  rw [source_multi_error_eq_squareError] at hraw
  have hnorm := normalized_full_bound _ ε
    (sourceArmCost e (B*e) he (mul_pos hB he) ha) (sourceArmCost e h he hh hb) C hε.le
    (sourceArmCost_nonneg _ _ _ _ _) (sourceArmCost_nonneg _ _ _ _ _) hC.le w hvar
    _ (fun _ => probability_nonneg _ _)
    (fun i => hcost e he hec' h x i hB' (fixed_other_small he hB' hM hmic) ha') hraw
  have hsimpl : 4*ε*C^k=δ/2 := by
    dsimp [ε]
    field_simp [ne_of_gt hC]
    ring
  exact hnorm.trans (by rw [hsimpl]; linarith)

#print axioms normalized_full_bound
#print axioms uniform_full_square_error
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization



