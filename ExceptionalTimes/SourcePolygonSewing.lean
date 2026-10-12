import ExceptionalTimes.SourcePolygonReading

/-! Full centered insertion sewing for literal polygon crossings and an
actual source success event. All small probability premises concern raw
fair fields, with the fixed-square mixed normalization. -/

open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.PolygonSewing
open DimerBinaryResponse EnvironmentVariance CenteredBlocks

def LocalChangeArms (Q : PolygonQuad) (P : Probe) : Prop :=
  ∀ ω a b : Configuration,
    (∀ v, v ∉ P.pocket → a v = b v) →
    Set.EqOn a ω P.region → Set.EqOn b ω P.region →
    Q.test a ≠ Q.test b → FourArms P ω

/-- Source Lemma 2.2 applies to the literal polygon tests when the
physical probe misses the actual frontier, with explicit mesh buffer. -/
theorem localChangeArms_of_no_frontier (hsource : PublishedPolygonBulkArms)
    (Q : PolygonQuad) (P : Probe) (he : 16*P.mesh<P.innerRadius)
    (havoid : ∀ p ∈ frontier Q.carrier,
      2*P.outerRadius<dist (position P.mesh P.center) (physicalHomeomorph P p)) :
    LocalChangeArms Q P := by
  intro ω a b hab ha hb hne
  apply polygon_fourArms_of_no_frontier hsource Q P he havoid ω a b hab ha hb
  exact fun h => hne ((Q.test_eq_iff a b).mpr h)

theorem nonzero_pair_change {Q : Type*} (quads : Q → PolygonQuad)
    (outer : (Q × Bool → Bool) → ℝ) (K : Kernel)
    (background : TwoTimeConfiguration) (x z : Site)
    (hne : rawPairResponse K background x z
      (fun η => outer (crossingVector quads η)) ≠ 0) :
    ∃ u v coin extra q t,
      (quads q).test (pairHistory background x z (u,v) (K u v coin extra) t) ≠
      (quads q).test (pairHistory background x z (u,v) (u,v) t) := by
  by_contra hn
  apply hne
  have heq : ∀ u v coin extra,
      crossingVector quads (pairHistory background x z (u,v) (K u v coin extra)) =
      crossingVector quads (pairHistory background x z (u,v) (u,v)) := by
    intro u v coin extra
    funext qt
    exact not_not.mp (fun h => hn ⟨u,v,coin,extra,qt.1,qt.2,h⟩)
  simp [rawPairResponse, heq]

/-- A raw nonzero joint-pair response supplies the source's actual
four-arm request on untouched fair colors, with no union over histories. -/
theorem pair_response_source_arm {Q : Type*} (quads : Q → PolygonQuad)
    (outer : (Q × Bool → Bool) → ℝ) (K : Kernel)
    (P : Probe) (z : Site) (ω : Configuration)
    (background : TwoTimeConfiguration)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hpair : P.center ∈ P.pocket ∧ P.center + z ∈ P.pocket)
    (hbackground : ∀ t, Set.EqOn (background t) ω P.region)
    (hne : rawPairResponse K background P.center z
      (fun η => outer (crossingVector quads η)) ≠ 0) : FourArms P ω := by
  obtain ⟨u,v,coin,extra,q,t,hchange⟩ :=
    nonzero_pair_change quads outer K background P.center z hne
  apply hlocal q ω _ _ _ _ _ hchange
  · intro y hy
    have hy₁ : y ≠ P.center := fun h => hy (h ▸ hpair.1)
    have hy₂ : y ≠ P.center + z := fun h => hy (h ▸ hpair.2)
    cases t <;> simp [pairHistory, putPair, hy₁, hy₂]
  · intro y hy
    have hy₁ : y ≠ P.center := fun h =>
      pocket_not_region P hpair.1 (h ▸ hy)
    have hy₂ : y ≠ P.center + z := fun h =>
      pocket_not_region P hpair.2 (h ▸ hy)
    cases t <;> simpa [pairHistory, putPair, hy₁, hy₂] using hbackground _ hy
  · intro y hy
    have hy₁ : y ≠ P.center := fun h =>
      pocket_not_region P hpair.1 (h ▸ hy)
    have hy₂ : y ≠ P.center + z := fun h =>
      pocket_not_region P hpair.2 (h ▸ hy)
    cases t <;> simpa [pairHistory, putPair, hy₁, hy₂] using hbackground _ hy

theorem square_response_source_arm {Q : Type*} (quads : Q → PolygonQuad)
    (outer : (Q × Bool → Bool) → ℝ) (P : Probe)
    (D : Finset Site) (ω : Configuration) (background : TwoTimeConfiguration)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hD : (D : Set Site) ⊆ P.pocket)
    (hbackground : ∀ t, Set.EqOn (background t) ω P.region)
    (hne : rawSquareResponse D background
      (fun η => outer (crossingVector quads η)) ≠ 0) : FourArms P ω := by
  by_contra hno
  have hconstant : ∀ h : History,
      crossingVector quads (squareHistory D background h) =
      crossingVector quads (squareHistory D background (false,false)) := by
    intro h
    funext qt
    by_contra hc
    apply hno
    apply hlocal qt.1 ω _ _ _ _ _ hc
    · intro v hv
      have hvD : v ∉ D := fun hmem => hv (hD hmem)
      simp [squareHistory, force, hvD]
    · intro v hv
      have hvD : v ∉ D := fun hmem => pocket_not_region P (hD hmem) hv
      simpa [squareHistory, force, hvD] using hbackground qt.2 hv
    · intro v hv
      have hvD : v ∉ D := fun hmem => pocket_not_region P (hD hmem) hv
      simpa [squareHistory, force, hvD] using hbackground qt.2 hv
  apply hne
  simp [rawSquareResponse, hconstant]

variable {I : Type*} [Fintype I] {H : I → Type*} [∀ i, Fintype (H i)]
noncomputable local instance : DecidableEq I := Classical.decEq _

theorem no_arm_pair_tests_constant {Q : Type*} (quads : Q → PolygonQuad)
    (P : Probe) (ω : Configuration) (A B : TwoTimeConfiguration) (x z : Site)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hchange : ∀ t, Set.EqOn (A t) (B t) P.pocketᶜ)
    (hA : ∀ t, Set.EqOn (A t) ω P.region)
    (hB : ∀ t, Set.EqOn (B t) ω P.region)
    (hx : x ∉ P.region) (hz : x+z ∉ P.region) (hna : ¬ FourArms P ω) :
    ∀ a b q t, (quads q).test (pairHistory A x z a b t)=
      (quads q).test (pairHistory B x z a b t) := by
  intro a b q t
  apply not_not.mp
  intro hne
  apply hna
  apply hlocal q ω _ _ _ _ _ hne
  · intro v hv
    cases t <;> exact putPair_congr_on _ _ x z _ _ _ (hchange _) hv
  · intro v hv
    have hvx : v≠x := fun he => hx (he ▸ hv)
    have hvz : v≠x+z := fun he => hz (he ▸ hv)
    cases t <;> simpa [pairHistory,putPair,hvx,hvz] using hA _ hv
  · intro v hv
    have hvx : v≠x := fun he => hx (he ▸ hv)
    have hvz : v≠x+z := fun he => hz (he ▸ hv)
    cases t <;> simpa [pairHistory,putPair,hvx,hvz] using hB _ hv

theorem no_arm_square_tests_constant {Q : Type*} (quads : Q → PolygonQuad)
    (P : Probe) (ω : Configuration) (A B : TwoTimeConfiguration) (D : Finset Site)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hchange : ∀ t, Set.EqOn (A t) (B t) P.pocketᶜ)
    (hA : ∀ t, Set.EqOn (A t) ω P.region)
    (hB : ∀ t, Set.EqOn (B t) ω P.region)
    (hD : ∀ v ∈ D, v ∉ P.region) (hna : ¬ FourArms P ω) :
    ∀ a q t, (quads q).test (squareHistory D A a t)=
      (quads q).test (squareHistory D B a t) := by
  intro a q t
  apply not_not.mp
  intro hne
  apply hna
  apply hlocal q ω _ _ _ _ _ hne
  · exact force_congr_on D _ _ _ _ (hchange t)
  · intro v hv
    have hvD : v ∉ D := fun h => hD v h hv
    simpa [squareHistory,force,hvD] using hA t hv
  · intro v hv
    have hvD : v ∉ D := fun h => hD v h hv
    simpa [squareHistory,force,hvD] using hB t hv

/-- Every OTHER centered insertion has its raw fair-field four-arm probe,
although the first insertion is still a jointly integrated two-site update.
No absolute value or sum over settings precedes this cancellation. -/
theorem multi_pair_nonzero_other_arms {Q : Type*} (quads : Q → PolygonQuad)
    (outer : (Q × Bool → Bool) → ℝ) (w : ∀ i, H i → ℝ) (K : Kernel)
    (A : (∀ i, H i) → TwoTimeConfiguration) (x z : Site) (ω : Configuration)
    (P : I → Probe) (hw : ∀ i, ∑ h, w i h=0)
    (hlocal : ∀ i q, LocalChangeArms (quads q) (P i))
    (hchange : ∀ i h a t, Set.EqOn (A (Function.update h i a) t) (A h t) (P i).pocketᶜ)
    (hfrozen : ∀ i h t, Set.EqOn (A h t) ω (P i).region)
    (hx : ∀ i, x ∉ (P i).region) (hz : ∀ i, x+z ∉ (P i).region)
    (hne : multiPairResponse w K A x z (fun ξ => outer (crossingVector quads ξ)) ≠ 0) :
    ∀ i, FourArms (P i) ω := by
  intro i
  by_contra hna
  apply hne
  apply kernel_zero_of_block_constant w _ i (hw i)
  intro h a
  have ht := no_arm_pair_tests_constant quads (P i) ω (A (Function.update h i a))
    (A h) x z (hlocal i) (hchange i h a) (hfrozen i _) (hfrozen i h) (hx i) (hz i) hna
  have hv : ∀ before after, crossingVector quads (pairHistory (A (Function.update h i a)) x z before after)=
      crossingVector quads (pairHistory (A h) x z before after) := by
    intro before after
    funext qt
    exact ht before after qt.1 qt.2
  simp only [rawPairResponse,hv]

theorem multi_square_nonzero_other_arms {Q : Type*} (quads : Q → PolygonQuad)
    (outer : (Q × Bool → Bool) → ℝ) (w : ∀ i, H i → ℝ) (D : Finset Site)
    (A : (∀ i, H i) → TwoTimeConfiguration) (ω : Configuration)
    (P : I → Probe) (hw : ∀ i, ∑ h, w i h=0)
    (hlocal : ∀ i q, LocalChangeArms (quads q) (P i))
    (hchange : ∀ i h a t, Set.EqOn (A (Function.update h i a) t) (A h t) (P i).pocketᶜ)
    (hfrozen : ∀ i h t, Set.EqOn (A h t) ω (P i).region)
    (hD : ∀ i v, v ∈ D → v ∉ (P i).region)
    (hne : multiSquareResponse w D A (fun ξ => outer (crossingVector quads ξ)) ≠ 0) :
    ∀ i, FourArms (P i) ω := by
  intro i
  by_contra hna
  apply hne
  apply kernel_zero_of_block_constant w _ i (hw i)
  intro h a
  have ht := no_arm_square_tests_constant quads (P i) ω (A (Function.update h i a))
    (A h) D (hlocal i) (hchange i h a) (hfrozen i _) (hfrozen i h) (hD i) hna
  have hv : ∀ c, crossingVector quads (squareHistory D (A (Function.update h i a)) c)=
      crossingVector quads (squareHistory D (A h) c) := by
    intro c
    funext qt
    exact ht c qt.1 qt.2
  simp only [rawSquareResponse,hv]

theorem source_multi_necessary {Λ : Finset Site} {QA QB : Type*}
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (mic sq : Probe) (z : Site) (D : Finset Site) (other : I → Probe)
    (geom : SourceOtherProbeGeometry endpoint mic sq z D other)
    (quadsA : QA → PolygonQuad) (quadsB : QB → PolygonQuad)
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

/-- The many-trial failure premise refers to the supplied actual source
event, and to raw first-point requests only. It contains no signed response. -/
def SourceEventFixedSquareFailure {Λ : Finset Site} {n : ℕ}
    (success : Fin n → Sources Λ → Bool) (mic sq : Probe) (a b ε : ℝ) : Prop :=
  probability (sourceLaw Λ) (fun ω =>
    AdaptiveExchange.select success (List.finRange n) ω=none ∧
    SourceE mic sq (complete ω.1) (complete ω.2)) ≤ ε*(a*b)

/-- Extra insertion factors are derived from independence of literal raw
coordinates; the actual source success event need only have its stated
finite support and source-exchange symmetry. -/
theorem source_event_failed_other_arms_bound {Λ : Finset Site} {n : ℕ}
    (layouts : Fin n → SourceSeamLayout) (success : Fin n → Sources Λ → Bool)
    (hsupported : ∀ j, SupportedSourceTest (layouts j).support (success j))
    (hswap : ∀ j ω, success j ω.swap=success j ω)
    (mic sq : Probe) (other : I → Probe)
    (S : Option I → Set ↥Λ) (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (htrial : ∀ j (v : ↥Λ), (v : Site) ∈ (layouts j).support → v ∈ S none)
    (hmic : ∀ v : ↥Λ, (v : Site) ∈ mic.region → v ∈ S none)
    (hsq : ∀ v : ↥Λ, (v : Site) ∈ sq.region → v ∈ S none)
    (hregion : ∀ i (v : ↥Λ), (v : Site) ∈ (other i).region → v ∈ S (some i))
    (a b ε : ℝ) (cost : I → ℝ)
    (hfailure : SourceEventFixedSquareFailure success mic sq a b ε)
    (hstatic : ∀ i, probability (sourceLaw Λ) (fun ω => FourArms (other i) (complete ω.1)) ≤ cost i)
    (reverse : Bool) :
    probability (sourceLaw Λ) (fun ω =>
      (AdaptiveExchange.select success (List.finRange n) ω=none ∧
        SourceOrientedE mic sq reverse ω) ∧ ∀ i, FourArms (other i) (complete ω.1)) ≤
      (ε*(a*b)) * ∏ i, cost i := by
  let E : Option I → Sources Λ → Prop := fun j ω => match j with
    | none => AdaptiveExchange.select success (List.finRange n) ω=none ∧
        SourceOrientedE mic sq reverse ω
    | some i => FourArms (other i) (complete ω.1)
  apply source_failure_product_bound S hdis E
  · intro j ω η heq
    cases j with
    | some i => exact fourArms_congr (other i) (source_complete_eqOn _ _ heq (hregion i)).1
    | none =>
      have htest : ∀ k, success k ω=success k η := by
        intro k
        exact hsupported k ω η (fun v hv => heq v (htrial k v hv))
      have hselect : AdaptiveExchange.select success (List.finRange n) ω =
          AdaptiveExchange.select success (List.finRange n) η := by
        unfold AdaptiveExchange.select
        congr 1
        funext k
        exact htest k
      have hm := source_complete_eqOn _ _ heq hmic
      have hs := source_complete_eqOn _ _ heq hsq
      change (_ ∧ SourceOrientedE mic sq reverse ω) ↔ (_ ∧ SourceOrientedE mic sq reverse η)
      rw [hselect]
      apply and_congr Iff.rfl
      cases reverse
      · exact and_congr (fourArms_congr mic hm.1) (fourArms_congr sq hs.2)
      · exact and_congr (fourArms_congr mic hm.2) (fourArms_congr sq hs.1)
  · cases reverse
    · exact hfailure
    · change probability (sourceLaw Λ) (fun ω =>
        AdaptiveExchange.select success (List.finRange n) ω=none ∧
        SourceE mic sq (complete ω.2) (complete ω.1)) ≤ ε*(a*b)
      rw [source_failure_symmetry _ _ hswap mic sq]
      exact hfailure
  · exact hstatic

/-- Full k-insertion comparison, k=|I|+1, for literal closed-cell polygon
observables. The only small-error input is the actual source event's
first-point relative failure at a_e*a_e,h. Ordinary source reading is
converted to pair/square algebra in SourcePolygonReading. -/
theorem source_full_centered_pair_square_bound
    {Λ : Finset Site} {n : ℕ} {QA QB : Type*}
    (layouts : Fin n → SourceSeamLayout) (success : Fin n → Sources Λ → Bool)
    (hsupported : ∀ j, SupportedSourceTest (layouts j).support (success j))
    (hswap : ∀ j ω, success j ω.swap=success j ω)
    (hinvariant : ∀ i ω, success i ω=true → ∀ j,
      success j (seamSwap (layouts i).inside ω)=success j ω)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule) (endpoint : I × Fin 2 ↪ Site)
    (mic sq : Probe) (z : Site) (D : Finset Site) (other : I → Probe)
    (geom : SourceOtherProbeGeometry endpoint mic sq z D other)
    (quadsA : QA → PolygonQuad) (quadsB : QB → PolygonQuad)
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
    (havoid : ∀ j i e, endpoint (i,e) ∉ (layouts j).inside ∧ endpoint (i,e) ∉ (layouts j).support)
    (hxtrial : ∀ j, mic.center ∈ (layouts j).pocket)
    (hztrial : ∀ j, mic.center+z ∈ (layouts j).pocket)
    (hDtrial : ∀ j, D ⊆ (layouts j).pocket)
    (hreading : ∀ j ω, success j ω=true → SourcePolygonSeamReading (layouts j) ω quadsA quadsB)
    (S : Option I → Set ↥Λ) (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (htrial : ∀ j (v : ↥Λ), (v : Site) ∈ (layouts j).support → v ∈ S none)
    (hmic : ∀ v : ↥Λ, (v : Site) ∈ mic.region → v ∈ S none)
    (hsq : ∀ v : ↥Λ, (v : Site) ∈ sq.region → v ∈ S none)
    (hregion : ∀ i (v : ↥Λ), (v : Site) ∈ (other i).region → v ∈ S (some i))
    (a b ε : ℝ) (cost : I → ℝ)
    (hfailure : SourceEventFixedSquareFailure success mic sq a b ε)
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
  have hgood : ∀ ω, AdaptiveExchange.select success (List.finRange n) ω≠none →
      L ω=R (AdaptiveExchange.applyFirst success
        (fun j => seamSwap (layouts j).inside) (List.finRange n) ω) := by
    intro ω hs
    cases hselect : AdaptiveExchange.select success (List.finRange n) ω with
    | none => exact False.elim (hs hselect)
    | some j =>
      simpa only [L,R,F,G,AdaptiveExchange.applyFirst,hselect] using
        source_reading_multi_overwrite (layouts j) quadsA quadsB outerA outerB
          w rule D mic.center z ω endpoint (havoid j) (hxtrial j) (hztrial j) (hDtrial j)
          (hreading j ω (AdaptiveExchange.selected_success _ _ ω j hselect))
  have hbad (reverse : Bool) : probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select success (List.finRange n) ω=none ∧ E reverse ω) ≤
      (ε*(a*b))*(∏ i, cost i) := by
    simpa only [E,and_assoc] using source_event_failed_other_arms_bound layouts success hsupported hswap
      mic sq other S hdis htrial hmic hsq hregion a b ε cost hfailure hstatic reverse
  have hb := adaptive_event_failure_weighting success
    (fun j => (layouts j).inside) (List.finRange n) hinvariant
    (E false) (E true) L R (2*V) (fun ω => (hdensity ω).1) (fun ω => (hdensity ω).2)
    (fun ω => (hnecessary ω).1) (fun ω => (hnecessary ω).2) hgood
  calc
    _ ≤ (2*V)*((ε*(a*b))*(∏ i, cost i)+(ε*(a*b))*(∏ i, cost i)) :=
      hb.trans (mul_le_mul_of_nonneg_left (add_le_add (hbad false) (hbad true)) (mul_nonneg (by norm_num) hV))
    _ = _ := by dsimp [V]; ring

#print axioms localChangeArms_of_no_frontier
#print axioms source_multi_necessary
#print axioms source_event_failed_other_arms_bound
#print axioms source_full_centered_pair_square_bound
end ExceptionalTimes.PairSquareSewing.PolygonSewing
