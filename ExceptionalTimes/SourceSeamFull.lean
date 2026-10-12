import ExceptionalTimes.SourceSeamCentered
import ExceptionalTimes.SourceSeamHistories

/-! The full centered k-insertion sewing error. Source inputs are restricted
to raw first-point failed-seam probability and ordinary one-probe costs. -/

open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing
open DimerBinaryResponse EnvironmentVariance CenteredBlocks

variable {I : Type*} [Fintype I]
noncomputable local instance : DecidableEq I := Classical.decEq _

abbrev SourceOtherHistory (I : Type*) := I → Bool → PairColor

noncomputable def sourceMultiLeft {Λ : Finset Site}
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (D : Finset Site) (x z : Site) (F G : TwoTimeConfiguration → ℝ) (ω : Sources Λ) : ℝ :=
  multiPairResponse w rule.kernel (overwriteSourceHistory endpoint (complete ω.1)) x z F *
    rawSquareResponse D (fun _ => complete ω.2) G

noncomputable def sourceMultiRight {Λ : Finset Site}
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (D : Finset Site) (x z : Site) (F G : TwoTimeConfiguration → ℝ) (ω : Sources Λ) : ℝ :=
  multiSquareResponse w D (overwriteSourceHistory endpoint (complete ω.1)) F *
    rawPairResponse rule.kernel (fun _ => complete ω.2) x z G

/-- The entire signed sum is exchanged on an actual successful source seam. -/
theorem source_success_multi_overwrite (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {QA QB : Type*} (J : SourceSeamLayout)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule)
    (D : Finset Site) (x z : Site) (ω : Sources Λ) (endpoint : I × Fin 2 ↪ Site)
    (havoid : ∀ i e, endpoint (i,e) ∉ J.inside ∧ endpoint (i,e) ∉ J.support)
    (hx : x ∈ J.pocket) (hz : x+z ∈ J.pocket) (hD : D ⊆ J.pocket)
    (hplaceA : J.QuadPlacement quadsA) (hplaceB : J.QuadPlacement quadsB)
    (hsuccess : J.success ω=true) :
    sourceMultiLeft w rule endpoint D x z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ)) ω =
      sourceMultiRight w rule endpoint D x z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ))
        (seamSwap J.inside ω) := by
  apply multi_successful_signed_exchange
  intro history
  obtain ⟨φ,ψ,f,g,hφ,hψ,hAF,hBG,hA'F,hB'G⟩ := source_success_transmitted_overwrite
    hexInput J quadsA quadsB outerA outerB D x z ω endpoint history havoid hx hz hD
      hplaceA hplaceB hsuccess
  exact successful_signed_exchange rule.kernel D x z _ _ _ _ _ _ φ ψ f g
    (rule.amplitude φ) (rule.response φ hφ) hψ hAF hBG hA'F hB'G

/-- The adaptive involution can retain any additional necessary events.
This is the same signed argument as the first-point theorem, before dropping
any of the other centered-insertion arm indicators. -/
theorem adaptive_event_failure_weighting {Λ : Finset Site} {J : Type*}
    (success : J → Sources Λ → Bool) (inside : J → Finset Site) (trials : List J)
    (hinvariant : ∀ i ω, success i ω=true → ∀ j,
      success j (seamSwap (inside i) ω)=success j ω)
    (E₁ E₂ : Sources Λ → Prop) (L R : Sources Λ → ℝ) (B : ℝ)
    (hL : ∀ ω, |L ω|≤B) (hR : ∀ ω, |R ω|≤B)
    (hsL : ∀ ω, L ω≠0 → E₁ ω) (hsR : ∀ ω, R ω≠0 → E₂ ω)
    (hgood : ∀ ω, AdaptiveExchange.select success trials ω≠none →
      L ω=R (AdaptiveExchange.applyFirst success (fun i => seamSwap (inside i)) trials ω)) :
    |(sourceLaw Λ).expect L-(sourceLaw Λ).expect R| ≤
      B*(probability (sourceLaw Λ) (fun ω => AdaptiveExchange.select success trials ω=none ∧ E₁ ω) +
        probability (sourceLaw Λ) (fun ω => AdaptiveExchange.select success trials ω=none ∧ E₂ ω)) := by
  let T := AdaptiveExchange.applyFirst success (fun i => seamSwap (inside i)) trials
  let N := fun ω => AdaptiveExchange.select success trials ω=none
  have hdiff : (sourceLaw Λ).expect L-(sourceLaw Λ).expect R =
      (sourceLaw Λ).expect (fun ω => if N ω then L ω-R ω else 0) := by
    rw [← adaptive_source_expect success inside trials hinvariant R,← FiniteLaw.expect_sub]
    apply FiniteLaw.expect_congr
    intro ω
    by_cases hn : N ω
    · have ht : T ω=ω := by
        have hs : AdaptiveExchange.select success trials ω=none := hn
        simp [T,AdaptiveExchange.applyFirst,hs]
      change L ω-R (T ω)=_
      simp [hn,ht]
    · have hg := hgood ω hn
      change L ω=R (T ω) at hg
      change L ω-R (T ω)=_
      simp [hn,hg]
  rw [hdiff]
  calc
    _ ≤ (sourceLaw Λ).expect (fun ω => |if N ω then L ω-R ω else 0|) :=
      FiniteLaw.abs_expect_le _ _
    _ ≤ (sourceLaw Λ).expect (fun ω => B*(EnvironmentVariance.indicator (N ω ∧ E₁ ω)+EnvironmentVariance.indicator (N ω ∧ E₂ ω))) := by
      apply FiniteLaw.expect_mono
      intro ω
      by_cases hn : N ω
      · have ha := abs_le_indicator_of_support L E₁ B hL hsL ω
        have hb := abs_le_indicator_of_support R E₂ B hR hsR ω
        simp only [ite_eq_left hn]
        simpa [EnvironmentVariance.indicator,hn,mul_add] using (abs_sub (L ω) (R ω)).trans (add_le_add ha hb)
      · simp [hn,EnvironmentVariance.indicator]
    _ = _ := by
      rw [FiniteLaw.expect_const_mul,FiniteLaw.expect_add]
      rfl

theorem kernel_nonzero_value {H : I → Type*} [∀ i, Fintype (H i)]
    (w : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) (hne : kernel w f≠0) :
    ∃ h, f h≠0 := by
  by_contra hn
  have hz : ∀ h, f h=0 := fun h => not_not.mp (fun hc => hn ⟨h,hc⟩)
  exact hne (by simp [kernel,hz])

/-- Total variation is taken only after the full signed sum; it bounds the
remaining density by twice the product variation. -/
theorem source_multi_density_bounds {Λ : Finset Site}
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (D : Finset Site) (x z : Site) (F G : TwoTimeConfiguration → ℝ)
    (hF : ∀ ξ, |F ξ|≤1) (hG : ∀ ξ, |G ξ|≤1) (ω : Sources Λ) :
    |sourceMultiLeft w rule endpoint D x z F G ω| ≤ 2*(∏ i, variation (w i)) ∧
    |sourceMultiRight w rule endpoint D x z F G ω| ≤ 2*(∏ i, variation (w i)) := by
  have hleft := kernel_variation_bound w (fun h =>
    rawPairResponse rule.kernel (overwriteSourceHistory endpoint (complete ω.1) h) x z F *
      rawSquareResponse D (fun _ => complete ω.2) G) 2
    (fun h => raw_product_bound rule.kernel D _ _ x z F G hF hG)
  have hright := kernel_variation_bound w (fun h =>
    rawSquareResponse D (overwriteSourceHistory endpoint (complete ω.1) h) F *
      rawPairResponse rule.kernel (fun _ => complete ω.2) x z G) 2
    (fun h => by simpa only [mul_comm] using (raw_product_bound rule.kernel D
      (fun _ => complete ω.2) (overwriteSourceHistory endpoint (complete ω.1) h) x z G F hG hF))
  constructor
  · simpa only [sourceMultiLeft,multiPairResponse,kernel,Finset.sum_mul,mul_assoc] using (hleft.trans_eq (mul_comm _ _))
  · simpa only [sourceMultiRight,multiSquareResponse,kernel,Finset.sum_mul,mul_assoc] using (hright.trans_eq (mul_comm _ _))

#print axioms source_success_multi_overwrite
#print axioms source_multi_density_bounds
#print axioms adaptive_event_failure_weighting

/-- Explicit placement of the OTHER dimers and all untouched arm regions.
Every field is a deterministic site membership statement. -/
structure SourceOtherProbeGeometry (endpoint : I × Fin 2 ↪ Site)
    (mic sq : Probe) (z : Site) (D : Finset Site) (other : I → Probe) : Prop where
  endpoint_in_pocket : ∀ i e, endpoint (i,e) ∈ (other i).pocket
  endpoint_not_mic : ∀ i e, endpoint (i,e) ∉ mic.region
  endpoint_not_sq : ∀ i e, endpoint (i,e) ∉ sq.region
  endpoint_not_other : ∀ j i e, endpoint (i,e) ∉ (other j).region
  first_not_other : ∀ i, mic.center ∉ (other i).region
  partner_not_other : ∀ i, mic.center+z ∉ (other i).region
  square_not_other : ∀ i v, v ∈ D → v ∉ (other i).region

/-- All k necessary requests are obtained from the actual full centered
coefficient. The settings witnessing different blocks may be different. -/
theorem source_multi_necessary {Λ : Finset Site} {QA QB : Type*}
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (mic sq : Probe) (z : Site) (D : Finset Site) (other : I → Probe)
    (geom : SourceOtherProbeGeometry endpoint mic sq z D other)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (hw : ∀ i, ∑ h, w i h=0)
    (hlocalAmic : ∀ q, LocalChangeArms (quadsA q) mic)
    (hlocalAsq : ∀ q, LocalChangeArms (quadsA q) sq)
    (hlocalBmic : ∀ q, LocalChangeArms (quadsB q) mic)
    (hlocalBsq : ∀ q, LocalChangeArms (quadsB q) sq)
    (hlocalOther : ∀ i q, LocalChangeArms (quadsA q) (other i))
    (hpair : mic.center ∈ mic.pocket ∧ mic.center+z ∈ mic.pocket)
    (hD : (D : Set Site) ⊆ sq.pocket) (ω : Sources Λ) :
    (sourceMultiLeft w rule endpoint D mic.center z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ)) ω≠0 →
      SourceOrientedE mic sq false ω ∧ ∀ i, FourArms (other i) (complete ω.1)) ∧
    (sourceMultiRight w rule endpoint D mic.center z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ)) ω≠0 →
      SourceOrientedE mic sq true ω ∧ ∀ i, FourArms (other i) (complete ω.1)) := by
  have hchange := fun i h a t => overwriteSourceHistory_block_change endpoint (complete ω.1)
    h i a (other i) (geom.endpoint_in_pocket i) t
  have hfreeze := fun i h t => overwriteSourceHistory_eqOn endpoint (complete ω.1) h
    (other i).region (geom.endpoint_not_other i) t
  have hmic := fun h t => overwriteSourceHistory_eqOn endpoint (complete ω.1) h
    mic.region geom.endpoint_not_mic t
  have hsq := fun h t => overwriteSourceHistory_eqOn endpoint (complete ω.1) h
    sq.region geom.endpoint_not_sq t
  constructor
  · intro hn
    have hp := mul_ne_zero_iff.mp hn
    have har := multi_pair_nonzero_other_arms quadsA outerA w rule.kernel
      (overwriteSourceHistory endpoint (complete ω.1)) mic.center z (complete ω.1)
      other hw hlocalOther hchange hfreeze geom.first_not_other geom.partner_not_other hp.1
    obtain ⟨h,hh⟩ := kernel_nonzero_value w _ hp.1
    exact ⟨⟨pair_response_source_arm quadsA outerA rule.kernel mic z (complete ω.1) _
        hlocalAmic hpair (hmic h) hh,
      square_response_source_arm quadsB outerB sq D (complete ω.2) _ hlocalBsq hD
        (fun _ _ _ => rfl) hp.2⟩,har⟩
  · intro hn
    have hp := mul_ne_zero_iff.mp hn
    have har := multi_square_nonzero_other_arms quadsA outerA w D
      (overwriteSourceHistory endpoint (complete ω.1)) (complete ω.1)
      other hw hlocalOther hchange hfreeze geom.square_not_other hp.1
    obtain ⟨h,hh⟩ := kernel_nonzero_value w _ hp.1
    exact ⟨⟨pair_response_source_arm quadsB outerB rule.kernel mic z (complete ω.2) _
        hlocalBmic hpair (fun _ _ _ => rfl) hp.2,
      square_response_source_arm quadsA outerA sq D (complete ω.1) _ hlocalAsq hD
        (hsq h) hh⟩,har⟩

#print axioms source_multi_necessary

/-- Full k-insertion sewing, with k=|I|+1. The other |I| centered histories
are summed before absolute values. The only small-error premise is the
published raw first-point failed-seam estimate at a_e*a_e,h; all other
factors are obtained by cancellation and disjoint-coordinate independence. -/
theorem source_full_centered_pair_square_bound (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {n : ℕ} {QA QB : Type*}
    (layouts : Fin n → SourceSeamLayout)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (mic sq : Probe) (z : Site) (D : Finset Site) (other : I → Probe)
    (geom : SourceOtherProbeGeometry endpoint mic sq z D other)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (hw : ∀ i, ∑ h, w i h=0)
    (hboundA : ∀ c, |outerA c|≤1) (hboundB : ∀ c, |outerB c|≤1)
    (hlocalAmic : ∀ q, LocalChangeArms (quadsA q) mic)
    (hlocalAsq : ∀ q, LocalChangeArms (quadsA q) sq)
    (hlocalBmic : ∀ q, LocalChangeArms (quadsB q) mic)
    (hlocalBsq : ∀ q, LocalChangeArms (quadsB q) sq)
    (hlocalOther : ∀ i q, LocalChangeArms (quadsA q) (other i))
    (hpair : mic.center ∈ mic.pocket ∧ mic.center+z ∈ mic.pocket)
    (hD : (D : Set Site) ⊆ sq.pocket)
    (hnested : ∀ i j, j=i ∨ (layouts j).support ⊆ (layouts i).inside ∨
      Disjoint (layouts j).support (layouts i).inside)
    (havoid : ∀ j i e, endpoint (i,e) ∉ (layouts j).inside ∧ endpoint (i,e) ∉ (layouts j).support)
    (hxtrial : ∀ j, mic.center ∈ (layouts j).pocket)
    (hztrial : ∀ j, mic.center+z ∈ (layouts j).pocket)
    (hDtrial : ∀ j, D ⊆ (layouts j).pocket)
    (hplaceA : ∀ j, (layouts j).QuadPlacement quadsA)
    (hplaceB : ∀ j, (layouts j).QuadPlacement quadsB)
    (S : Option I → Set ↥Λ) (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (htrial : ∀ j (v : ↥Λ), (v : Site) ∈ (layouts j).support → v ∈ S none)
    (hmic : ∀ v : ↥Λ, (v : Site) ∈ mic.region → v ∈ S none)
    (hsq : ∀ v : ↥Λ, (v : Site) ∈ sq.region → v ∈ S none)
    (hregion : ∀ i (v : ↥Λ), (v : Site) ∈ (other i).region → v ∈ S (some i))
    (a b ε : ℝ) (cost : I → ℝ)
    (hfailure : SourceFixedSquareFailure (Λ := Λ) layouts mic sq a b ε)
    (hstatic : ∀ i, probability (sourceLaw Λ) (fun ω => FourArms (other i) (complete ω.1)) ≤ cost i) :
    |(sourceLaw Λ).expect (sourceMultiLeft w rule endpoint D mic.center z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ))) -
      (sourceLaw Λ).expect (sourceMultiRight w rule endpoint D mic.center z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ)))| ≤
      4*(∏ i, variation (w i))*ε*(a*b)*(∏ i, cost i) := by
  let F := fun ξ => outerA (crossingVector quadsA ξ)
  let G := fun ξ => outerB (crossingVector quadsB ξ)
  let L := sourceMultiLeft w rule endpoint D mic.center z F G (Λ := Λ)
  let R := sourceMultiRight w rule endpoint D mic.center z F G (Λ := Λ)
  let V := ∏ i, variation (w i)
  let E : Bool → Sources Λ → Prop := fun reverse ω => SourceOrientedE mic sq reverse ω ∧
    ∀ i, FourArms (other i) (complete ω.1)
  have hV : 0≤V := Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun h _ => abs_nonneg (w i h)))
  have hdensity := fun (ω : Sources Λ) => source_multi_density_bounds w rule endpoint D mic.center z F G
    (fun _ => hboundA _) (fun _ => hboundB _) ω
  have hnecessary := fun (ω : Sources Λ) => source_multi_necessary w rule endpoint mic sq z D other geom
    quadsA quadsB outerA outerB hw hlocalAmic hlocalAsq hlocalBmic hlocalBsq hlocalOther hpair hD ω
  have hgood : ∀ ω, AdaptiveExchange.select (fun j => (layouts j).success) (List.finRange n) ω≠none →
      L ω=R (AdaptiveExchange.applyFirst (fun j => (layouts j).success)
        (fun j => seamSwap (layouts j).inside) (List.finRange n) ω) := by
    intro ω hs
    cases hselect : AdaptiveExchange.select (fun j => (layouts j).success) (List.finRange n) ω with
    | none => exact False.elim (hs hselect)
    | some j =>
      simpa only [L,R,F,G,AdaptiveExchange.applyFirst,hselect] using
        source_success_multi_overwrite hexInput (layouts j) quadsA quadsB outerA outerB
          w rule D mic.center z ω endpoint (havoid j) (hxtrial j) (hztrial j) (hDtrial j)
          (hplaceA j) (hplaceB j) (AdaptiveExchange.selected_success _ _ ω j hselect)
  have hbad (reverse : Bool) : probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select (fun j => (layouts j).success) (List.finRange n) ω=none ∧ E reverse ω) ≤
      (ε*(a*b))*(∏ i, cost i) := by
    simpa only [E,and_assoc] using source_failed_other_arms_bound layouts mic sq other S hdis
      htrial hmic hsq hregion a b ε cost hfailure hstatic reverse
  have hb := adaptive_event_failure_weighting (fun j => (layouts j).success)
    (fun j => (layouts j).inside) (List.finRange n) (source_layouts_invariant layouts hnested)
    (E false) (E true) L R (2*V) (fun ω => (hdensity ω).1) (fun ω => (hdensity ω).2)
    (fun ω => (hnecessary ω).1) (fun ω => (hnecessary ω).2) hgood
  calc
    _ ≤ (2*V)*((ε*(a*b))*(∏ i, cost i)+(ε*(a*b))*(∏ i, cost i)) :=
      hb.trans (mul_le_mul_of_nonneg_left (add_le_add (hbad false) (hbad true)) (mul_nonneg (by norm_num) hV))
    _ = _ := by dsimp [V]; ring

#print axioms source_full_centered_pair_square_bound


noncomputable def averagedMultiPairResponse (Λ : Finset Site)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (x z : Site) (F : TwoTimeConfiguration → ℝ) : ℝ :=
  (ProbeProduct.fairSites ↥Λ).expect (fun ω =>
    multiPairResponse w rule.kernel (overwriteSourceHistory endpoint (complete ω)) x z F)

noncomputable def averagedMultiSquareResponse (Λ : Finset Site)
    (w : I → (Bool → PairColor) → ℝ) (endpoint : I × Fin 2 ↪ Site)
    (D : Finset Site) (F : TwoTimeConfiguration → ℝ) : ℝ :=
  (ProbeProduct.fairSites ↥Λ).expect (fun ω =>
    multiSquareResponse w D (overwriteSourceHistory endpoint (complete ω)) F)

/-- The full k-insertion source expression is exactly the common-square
error in the actual averaged coefficients, with the SAME square calibrator. -/
theorem source_multi_error_eq_squareError (Λ : Finset Site)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (D : Finset Site) (x z : Site) (F G : TwoTimeConfiguration → ℝ) :
    (sourceLaw Λ).expect (sourceMultiLeft w rule endpoint D x z F G) -
      (sourceLaw Λ).expect (sourceMultiRight w rule endpoint D x z F G) =
      CommonSquare.squareError (averagedMultiPairResponse Λ w rule endpoint x z F)
        (averagedPairResponse Λ rule x z G) (averagedMultiSquareResponse Λ w endpoint D F)
        (averagedSquareResponse Λ D G) := by
  unfold sourceMultiLeft sourceMultiRight
  rw [source_expect_product (fun ω =>
      multiPairResponse w rule.kernel (overwriteSourceHistory endpoint (complete ω)) x z F)
      (fun ω => rawSquareResponse D (fun _ => complete ω) G),
    source_expect_product (fun ω =>
      multiSquareResponse w D (overwriteSourceHistory endpoint (complete ω)) F)
      (fun ω => rawPairResponse rule.kernel (fun _ => complete ω) x z G)]
  rfl

/-- In particular, one arm cost C*a per other insertion gives exactly
normalization a^k*b for k=|I|+1. -/
theorem source_full_normalization (err V ε a b C : ℝ) (ha : 0<a) (hb : 0<b)
    (h : |err| ≤ 4*V*ε*(a*b)*(∏ _i : I, C*a)) :
    |err| / (a^(Fintype.card I+1)*b) ≤ 4*V*ε*C^(Fintype.card I) := by
  apply (div_le_iff₀ (mul_pos (pow_pos ha _) hb)).mpr
  convert h using 1
  simp only [Finset.prod_const,Finset.card_univ,mul_pow,pow_succ]
  ring

#print axioms source_multi_error_eq_squareError
#print axioms source_full_normalization

end ExceptionalTimes.PairSquareSewing


