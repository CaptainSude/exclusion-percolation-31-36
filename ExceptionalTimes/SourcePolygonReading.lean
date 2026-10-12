import ExceptionalTimes.SourceSeamFull
import ExceptionalTimes.PolygonInteriorProbe

/-! Ordinary polygon reading of source06 Lemma 6.5, followed by the
checked pair/square and full-centered-history algebra. The input is only
one-time color dependence on the actual inner-disk black-run join bit.
The probability/source-event scope is supplied separately. -/

open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.PolygonSewing
open DimerBinaryResponse EnvironmentVariance CenteredBlocks

noncomputable def crossingVector {Q : Type*} (quads : Q → PolygonQuad)
    (ω : TwoTimeConfiguration) : Q × Bool → Bool := fun qt => (quads qt.1).test (ω qt.2)

def NecklaceCrossingDependence {Q : Type*} (quads : Q → PolygonQuad)
    (D : Finset Site) (x z : Site) (pairBackground squareBackground : TwoTimeConfiguration)
    (φ : Table) (ψ : Bool → Bool) : Prop :=
  ∀ q t a b, annotationBit φ ψ a = annotationBit φ ψ b →
    (quads q).test (annotationConfiguration D x z pairBackground squareBackground t a) =
      (quads q).test (annotationConfiguration D x z pairBackground squareBackground t b)

theorem crossing_dependence_transmissions {Q : Type*} (quads : Q → PolygonQuad)
    (outer : (Q × Bool → Bool) → ℝ) (D : Finset Site) (x z : Site)
    (pairBackground squareBackground : TwoTimeConfiguration)
    (φ : Table) (ψ : Bool → Bool)
    (h : NecklaceCrossingDependence quads D x z pairBackground squareBackground φ ψ) :
    ∃ f : History → ℝ,
      PairTransmission pairBackground x z (fun ξ => outer (crossingVector quads ξ)) φ f ∧
      SquareTransmission D squareBackground (fun ξ => outer (crossingVector quads ξ)) ψ f := by
  let read := fun q t => booleanReading (annotationBit φ ψ)
    (fun a => (quads q).test (annotationConfiguration D x z pairBackground squareBackground t a))
  let f := fun history : History => outer (fun qt => read qt.1 qt.2
    (if qt.2 then history.2 else history.1))
  refine ⟨f, ?_, ?_⟩
  · intro a b
    apply congrArg outer
    funext qt
    cases ht : qt.2
    · simpa [crossingVector, pairHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 false) (.inl a)).symm
    · simpa [crossingVector, pairHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 true) (.inl b)).symm
  · intro history
    apply congrArg outer
    funext qt
    cases ht : qt.2
    · simpa [crossingVector, squareHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 false) (.inr history.1)).symm
    · simpa [crossingVector, squareHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 true) (.inr history.2)).symm

theorem transmittedAnnotations_of_plane_necklace_dependence
    {QA QB : Type*} (quadsA : QA → PolygonQuad) (quadsB : QB → PolygonQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (D : Finset Site) (x z : Site) (A B A' B' : TwoTimeConfiguration)
    (pairInner squareInner : NecklaceShape) (ω η : Configuration)
    (hA : NecklaceCrossingDependence quadsA D x z A A'
      (planePairJoinTable pairInner ω x z) (planeSquareJoin squareInner η D))
    (hB : NecklaceCrossingDependence quadsB D x z B' B
      (planePairJoinTable pairInner ω x z) (planeSquareJoin squareInner η D)) :
    TransmittedAnnotations D x z A B A' B'
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  obtain ⟨f,hAF,hA'F⟩ := crossing_dependence_transmissions quadsA outerA D x z A A' _ _ hA
  obtain ⟨g,hB'G,hBG⟩ := crossing_dependence_transmissions quadsB outerB D x z B' B _ _ hB
  exact ⟨planePairJoinTable pairInner ω x z,planeSquareJoin squareInner η D,f,g,
    planePairJoinTable_increasing pairInner ω x z,planeSquareJoin_increasing squareInner η D,
    hAF,hBG,hA'F,hB'G⟩

def SourceOneTimeReading {Q : Type*} (quads : Q → PolygonQuad)
    (pocket : Finset Site) (inner : Bool → NecklaceShape)
    (background : Bool → TwoTimeConfiguration) : Prop :=
  ∀ q t a b ξ η,
    Set.EqOn ξ (background a t) (pocket : Set Site)ᶜ →
    Set.EqOn η (background b t) (pocket : Set Site)ᶜ →
    (inner a).planeJoinBit ξ=(inner b).planeJoinBit η →
    (quads q).test ξ=(quads q).test η

theorem source_reading_pair_square_dependence {Q : Type*} (quads : Q → PolygonQuad)
    (pocket D : Finset Site) (x z : Site)
    (hx : x ∈ pocket) (hz : x+z ∈ pocket) (hD : D ⊆ pocket)
    (inner : Bool → NecklaceShape) (background : Bool → TwoTimeConfiguration)
    (raw : Bool → Configuration)
    (hfrozen : ∀ a t, Set.EqOn (background a t) (raw a) (inner a).insideSites)
    (hread : SourceOneTimeReading quads pocket inner background) :
    NecklaceCrossingDependence quads D x z (background false) (background true)
      (planePairJoinTable (inner false) (raw false) x z)
      (planeSquareJoin (inner true) (raw true) D) := by
  intro q t a b hab
  apply hread q t (annotationSource a) (annotationSource b)
    (annotationConfiguration D x z (background false) (background true) t a)
    (annotationConfiguration D x z (background false) (background true) t b)
    (annotation_agrees_outside_pocket pocket D x z hx hz hD background t a)
    (annotation_agrees_outside_pocket pocket D x z hx hz hD background t b)
  have hjoin (c : InteriorAnnotation) := annotation_inner_join (inner false) (inner true)
    D x z (background false) (background true) (raw false) (raw true)
    (hfrozen false) (hfrozen true) t c
  have hinner (c : InteriorAnnotation) :
      inner (annotationSource c)=annotationInner (inner false) (inner true) c := by
    cases c <;> rfl
  rw [hinner a,hinner b,hjoin a,hjoin b]
  exact hab

/-- Two ordinary source readings give the four transmitted evaluations
used by the checked signed exchange theorem. All pair-specific content is
proved here from local overwrites and the finite monotone truth table. -/
theorem source_readings_transmitted {QA QB : Type*}
    (quadsA : QA → PolygonQuad) (quadsB : QB → PolygonQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (pocket D : Finset Site) (x z : Site)
    (hx : x ∈ pocket) (hz : x+z ∈ pocket) (hD : D ⊆ pocket)
    (inner : Bool → NecklaceShape) (raw : Bool → Configuration)
    (A B A' B' : TwoTimeConfiguration)
    (hfreezeA : ∀ t, Set.EqOn (A t) (raw false) (inner false).insideSites)
    (hfreezeB : ∀ t, Set.EqOn (B t) (raw true) (inner true).insideSites)
    (hfreezeA' : ∀ t, Set.EqOn (A' t) (raw true) (inner true).insideSites)
    (hfreezeB' : ∀ t, Set.EqOn (B' t) (raw false) (inner false).insideSites)
    (hreadA : SourceOneTimeReading quadsA pocket inner (fun a => if a then A' else A))
    (hreadB : SourceOneTimeReading quadsB pocket inner (fun a => if a then B else B')) :
    TransmittedAnnotations D x z A B A' B'
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  apply transmittedAnnotations_of_plane_necklace_dependence quadsA quadsB outerA outerB
    D x z A B A' B' (inner false) (inner true) (raw false) (raw true)
  · apply source_reading_pair_square_dependence quadsA pocket D x z hx hz hD inner
      (fun a => if a then A' else A) raw
    · intro a t
      cases a
      · exact hfreezeA t
      · exact hfreezeA' t
    · exact hreadA
  · apply source_reading_pair_square_dependence quadsB pocket D x z hx hz hD inner
      (fun a => if a then B else B') raw
    · intro a t
      cases a
      · exact hfreezeB' t
      · exact hfreezeB t
    · exact hreadB

/-- The ordinary source reading is quantified over all fixed exterior
histories. Both source interiors have actual necklace disks inside the
literal exchanged cut. Success probabilities are deliberately absent.

A source adapter must establish this predicate on its actual source event;
this definition is not an assertion for arbitrary layouts or polygons. -/
def SourcePolygonSeamReading {Λ : Finset Site} {QA QB : Type*}
    (J : SourceSeamLayout) (ω : Sources Λ)
    (quadsA : QA → PolygonQuad) (quadsB : QB → PolygonQuad) : Prop :=
  ∃ inner : Bool → NecklaceShape,
    (∀ a, (inner a).insideSites ⊆ (J.inside : Set Site)) ∧
    (∀ background : Bool → TwoTimeConfiguration,
      (∀ a t, Set.EqOn (background a t)
        (complete (sewnField J.inside ω a false)) (J.support : Set Site)) →
      (∀ a b t, Set.EqOn (background a t) (background b t) (J.inside : Set Site)ᶜ) →
      SourceOneTimeReading quadsA J.pocket inner background) ∧
    (∀ background : Bool → TwoTimeConfiguration,
      (∀ a t, Set.EqOn (background a t)
        (complete (sewnField J.inside ω a true)) (J.support : Set Site)) →
      (∀ a b t, Set.EqOn (background a t) (background b t) (J.inside : Set Site)ᶜ) →
      SourceOneTimeReading quadsB J.pocket inner background)

/-- Applying the published ordinary reading to actual endpoint overwrites
produces the monotone tables and all four response evaluation equalities. -/
theorem source_reading_transmitted_overwrite {I : Type*}
    {Λ : Finset Site} {QA QB : Type*} (J : SourceSeamLayout)
    (quadsA : QA → PolygonQuad) (quadsB : QB → PolygonQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (D : Finset Site) (x z : Site) (ω : Sources Λ)
    (endpoint : I × Fin 2 ↪ Site) (history : I → Bool → PairColor)
    (havoid : ∀ i e, endpoint (i,e) ∉ J.inside ∧ endpoint (i,e) ∉ J.support)
    (hx : x ∈ J.pocket) (hz : x+z ∈ J.pocket) (hD : D ⊆ J.pocket)
    (hreading : SourcePolygonSeamReading J ω quadsA quadsB) :
    TransmittedAnnotations D x z
      (overwriteSourceHistory endpoint (complete ω.1) history) (fun _ => complete ω.2)
      (overwriteSourceHistory endpoint (complete (seamSwap J.inside ω).1) history)
      (fun _ => complete (seamSwap J.inside ω).2)
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  obtain ⟨inner,hinside,hreadingA,hreadingB⟩ := hreading
  have hsewn (a b exterior : Bool) : Set.EqOn
      (complete (sewnField J.inside ω a exterior))
      (complete (sewnField J.inside ω b exterior)) (J.inside : Set Site)ᶜ := by
    intro v hv
    have hvIn : v ∉ J.inside := hv
    by_cases hvΛ : v ∈ Λ <;> simp [complete,sewnField,hvΛ,hvIn]
  have hreadA : SourceOneTimeReading quadsA J.pocket inner
      (fun a => overwriteSourceHistory endpoint (complete (sewnField J.inside ω a false)) history) := by
    apply hreadingA
    · intro a t
      exact overwriteSourceHistory_eqOn endpoint _ history (J.support : Set Site)
        (fun i e => (havoid i e).2) t
    · intro a b t
      exact overwriteSourceHistory_congr endpoint _ _ history _ (hsewn a b false) t
  have hreadB : SourceOneTimeReading quadsB J.pocket inner
      (fun a _ => complete (sewnField J.inside ω a true)) := by
    apply hreadingB
    · intro a t v hv
      rfl
    · intro a b t
      exact hsewn a b true
  have hfreeze (a b t : Bool) : Set.EqOn
      (overwriteSourceHistory endpoint (complete (sewnField J.inside ω a b)) history t)
      (complete (if a then ω.2 else ω.1)) (inner a).insideSites := by
    apply (overwriteSourceHistory_eqOn endpoint _ history (inner a).insideSites _ t).trans
      (source_sewn_frozen J ω a b (inner a) (hinside a))
    intro i e hv
    exact (havoid i e).1 (hinside a hv)
  have hfreezeRaw (a b : Bool) := source_sewn_frozen J ω a b (inner a) (hinside a)
  have hs0 : sewnField J.inside ω false false=ω.1 := by funext v; simp [sewnField]
  have hs1 : sewnField J.inside ω true true=ω.2 := by funext v; simp [sewnField]
  have hs10 : sewnField J.inside ω true false=(seamSwap J.inside ω).1 := rfl
  have hs01 : sewnField J.inside ω false true=(seamSwap J.inside ω).2 := rfl
  apply source_readings_transmitted quadsA quadsB outerA outerB J.pocket D x z hx hz hD
    inner (fun a => complete (if a then ω.2 else ω.1))
  · simpa only [hs0] using hfreeze false false
  · intro t
    simpa only [hs1] using hfreezeRaw true true
  · simpa only [hs10] using hfreeze true false
  · intro t
    simpa only [hs01] using hfreezeRaw false true
  · convert hreadA using 1
    funext a t
    cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,hs0,hs10]
  · convert hreadB using 1
    funext a t
    cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,hs1,hs01]

/-- The full centered signed history sum is exchanged before absolute
values. This introduces no k-point probability input. -/
theorem source_reading_multi_overwrite {I : Type*} [Fintype I]
    {Λ : Finset Site} {QA QB : Type*} (J : SourceSeamLayout)
    (quadsA : QA → PolygonQuad) (quadsB : QB → PolygonQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule)
    (D : Finset Site) (x z : Site) (ω : Sources Λ) (endpoint : I × Fin 2 ↪ Site)
    (havoid : ∀ i e, endpoint (i,e) ∉ J.inside ∧ endpoint (i,e) ∉ J.support)
    (hx : x ∈ J.pocket) (hz : x+z ∈ J.pocket) (hD : D ⊆ J.pocket)
    (hreading : SourcePolygonSeamReading J ω quadsA quadsB) :
    sourceMultiLeft w rule endpoint D x z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ)) ω =
      sourceMultiRight w rule endpoint D x z
        (fun ξ => outerA (crossingVector quadsA ξ)) (fun ξ => outerB (crossingVector quadsB ξ))
        (seamSwap J.inside ω) := by
  apply multi_successful_signed_exchange
  intro history
  obtain ⟨φ,ψ,f,g,hφ,hψ,hAF,hBG,hA'F,hB'G⟩ := source_reading_transmitted_overwrite
    J quadsA quadsB outerA outerB D x z ω endpoint history havoid hx hz hD hreading
  exact successful_signed_exchange rule.kernel D x z _ _ _ _ _ _ φ ψ f g
    (rule.amplitude φ) (rule.response φ hφ) hψ hAF hBG hA'F hB'G

#print axioms source_reading_transmitted_overwrite
#print axioms source_reading_multi_overwrite
end ExceptionalTimes.PairSquareSewing.PolygonSewing
