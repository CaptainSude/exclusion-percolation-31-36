import ExceptionalTimes.SourceSewingTrialPlacement

/-! Application of the source's actual finite trials to the complete
centered coefficient. All placements, local-change tests, coordinate
independence and adaptive invariance are proved from the source geometry. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
open PolygonSewing EnvironmentVariance CenteredBlocks

theorem fixed_other_small {e B M R : ℝ} (he : 0<e) (hB : 0<B)
    (hM : 64≤M) (hsmall : 4*(M*(B*e))<R) : 4*(64*(B*e))<R := by
  nlinarith [mul_pos hB he]

noncomputable def fixedOtherProbe {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (B : ℝ) (hB : 0<B)
    (hsmall : 4*(64*(B*e))<outerRadius G) (x : Site) : Probe :=
  microProbe e he x B 64 (outerRadius G) hB (by norm_num) hsmall

/-- The complete k+1-insertion error, with every other arm probability
retained. This theorem uses the source first-point bound exactly at a*b. -/
theorem SourceTrials.full_centered_bound
    {q k n : ℕ} {G : SourceSeparatedGeometry q k} {B M ε : ℝ}
    {hB : 0<B} {hM : 0<M} {radii : Fin n→ℝ} {L : ℝ}
    {hr : ∀i,0<radii i} {hL : 1≤L}
    {h e : ℝ} {hh : 0<h} {he : 0<e} {x : Fin (k+1)→Site}
    {hmic : 4*(M*(B*e))<outerRadius G} {hsq : 4*(8*h)<outerRadius G}
    {ha : 4*(B*e)<1} {hb : 4*h<1}
    (T : SourceTrials G B M ε hB hM n radii L hr hL h e hh he x hmic hsq ha hb)
    (hbulk : PublishedPolygonBulkArms) (hBlarge : 128≤B) (hMlarge : 64≤M)
    (hx : G.Admissible e x) (hesmall : e<h/4)
    (houter : ∀i,L*radii i<outerRadius G)
    (hsep : ∀i j,i<j→L*radii i<radii j/L)
    (hbuffer : ∀i,64*(M*(B*e)+h)<radii i/L)
    (z : Site) (hz : ‖triangularEmbedding z‖≤B)
    (endpoint : Fin k×Fin 2 ↪ Site)
    (hfirst : ∀i,endpoint (i,0)=x i.succ) (hsecond : ∀i,endpoint (i,1)=x i.succ+z)
    (w : Fin k→(Bool→PairColor)→ℝ) (rule : Rule)
    (hw : ∀i,∑a,w i a=0)
    (outerA : (Fin q×Bool→Bool)→ℝ) (outerB : (Unit×Bool→Bool)→ℝ)
    (hboundA : ∀c,|outerA c|≤1) (hboundB : ∀c,|outerB c|≤1) :
    let Λ := sample G e he x h
    let D := sourceSquareSites e he (x 0) h
    let F := fun ξ => outerA (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)
    let H := fun ξ => outerB (PolygonSewing.crossingVector (fun _ : Unit => sourceReferenceAt e he (x 0)) ξ)
    let other := fun i : Fin k => fixedOtherProbe G e he B hB (fixed_other_small he hB hMlarge hmic) (x i.succ)
    |(sourceLaw Λ).expect (sourceMultiLeft w rule endpoint D (x 0) z F H)-
      (sourceLaw Λ).expect (sourceMultiRight w rule endpoint D (x 0) z F H)|≤
      4*(∏i,variation (w i))*ε*
        (sourceArmCost e (B*e) he (mul_pos hB he) ha*sourceArmCost e h he hh hb)*
        (∏i,probability (sourceLaw Λ) (fun ω => FourArms (other i) (complete ω.1))) := by
  dsimp only
  let mic := microProbe e he (x 0) B M (outerRadius G) hB hM hmic
  let sq := squareProbe e he (x 0) h (outerRadius G) hh hsq
  let other := fun i : Fin k => fixedOtherProbe G e he B hB
    (fixed_other_small he hB hMlarge hmic) (x i.succ)
  have hBe : 0<B*e := mul_pos hB he
  have hBeR : B*e<outerRadius G := by nlinarith
  have hinnerMic : 16*e<mic.innerRadius := by
    change 16*e<M*(B*e)
    have hbe : 128*e≤B*e := by nlinarith
    nlinarith
  have hinnerSq : 16*e<sq.innerRadius := by change 16*e<8*h; linarith
  have hinnerOther (i : Fin k) : 16*e<(other i).innerRadius := by
    change 16*e<64*(B*e)
    nlinarith
  have hpockets := first_insertions_in_trial_pockets G e h B M he hh hBlarge hMlarge hesmall
    hmic x z hz radii L hr hL hbuffer T.annuli
  apply PolygonSewing.source_full_centered_pair_square_bound
    (S := sourceCoordinates G e x (sample G e he x h))
    (T.annuli.layout hr hL) T.success T.supported T.source_swap (T.adaptive_invariance hsep)
    w rule endpoint mic sq z (sourceSquareSites e he (x 0) h) other
  · exact source_other_geometry G e h B M he hh hBlarge hMlarge hesmall hmic hsq x hx z hz
      endpoint hfirst hsecond mic sq other rfl rfl rfl rfl rfl rfl
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · exact hw
  · exact hboundA
  · exact hboundB
  · exact source_quad_localChange G hbulk e he x hx 0 mic rfl rfl rfl hinnerMic
  · exact source_quad_localChange G hbulk e he x hx 0 sq rfl rfl rfl hinnerSq
  · intro _
    exact source_reference_localChange G hbulk e he (x 0) mic rfl rfl rfl hinnerMic
  · intro _
    exact source_reference_localChange G hbulk e he (x 0) sq rfl rfl rfl hinnerSq
  · intro i
    exact source_quad_localChange G hbulk e he x hx i.succ (other i) rfl rfl rfl (hinnerOther i)
  · apply pair_fits_pocket mic
    change |e| *‖triangularEmbedding z‖<M*(B*e)/2
    rw [abs_of_pos he]
    have hez : e*‖triangularEmbedding z‖≤B*e := by nlinarith
    nlinarith
  · exact sourceSquareSites_subset_pocket sq h (by change 2*e+2*h<8*h/2; linarith)
  · exact other_endpoints_avoid_trials G e h B he hBeR x hx z hz endpoint hfirst hsecond
      radii L hr hL houter T.annuli
  · exact hpockets.1
  · exact hpockets.2.1
  · exact hpockets.2.2
  · exact T.reading
  · exact sourceCoordinates_disjoint G e x hx _
  · exact trial_coordinates G e h he x radii L hr hL houter T.annuli
  · exact probe_coordinates G e x _ none mic rfl rfl rfl
  · exact probe_coordinates G e x _ none sq rfl rfl rfl
  · intro i
    exact probe_coordinates G e x _ (some i) (other i) rfl rfl rfl
  · exact T.failure
  · intro i
    exact le_rfl

#print axioms SourceTrials.full_centered_bound
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization



