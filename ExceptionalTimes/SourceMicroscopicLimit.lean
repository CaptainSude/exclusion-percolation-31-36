import ExceptionalTimes.SourceMicroscopicSample

/-! Mesh-only uniform microscopic comparison obtained by fixing one
source square after the tolerance, then eliminating its sample dependence. -/
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CenteredBlocks

/-- The actual compact-separated microscopic coefficient comparison.
All source geometry, full centered sewing and square cancellation have
already been proved; no limiting finite-quad transfer is assumed. -/
theorem uniform_microscopic_two_rule_error {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) :
    ∀δ : ℝ,0<δ→∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
      ∀x : Fin (k+1)→Site,G.Admissible e x→∀z : Site,‖triangularEmbedding z‖≤B→
      ∀endpoint : Fin k×Fin 2 ↪ Site,
      (∀i,endpoint (i,0)=x i.succ)→(∀i,endpoint (i,1)=x i.succ+z)→
      ∀w : Fin k→(Bool→PairColor)→ℝ,(∀i,∑a,w i a=0)→(∀i,variation (w i)≤1)→
      ∀r₁ r₂ : Rule,∀outer : (Fin q×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→
      ∀hB : 0<B,∀ha : 4*(B*e)<1,
      |microscopicTwoRuleError G e he x z endpoint w r₁ r₂ outer|/
        (sourceArmCost e (B*e) he (mul_pos hB he) ha)^(k+2)<δ := by
  intro δ hδ
  obtain ⟨h0,hh0,hbound⟩ := uniform_two_rule_error G B hseams hstatic hbulk hlower harmlower δ hδ
  obtain ⟨e0,he0,hbound⟩ := hbound (h0/2) (half_pos hh0) (by linarith)
  refine ⟨e0,he0,?_⟩
  intro e he he0' x hx z hz endpoint hfirst hsecond w hw hvar r₁ r₂ outer hout hB ha
  rw [←twoRuleError_eq_microscopic G e he x (h0/2) z endpoint w r₁ r₂ outer]
  exact hbound e he he0' x hx z hz endpoint hfirst hsecond w hw hvar r₁ r₂ outer hout hB ha

#print axioms uniform_microscopic_two_rule_error
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization
