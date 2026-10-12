import ExceptionalTimes.SourceSeamInputs
import ExceptionalTimes.DimerProbeWitness

/-! Literal other-dimer histories are fixed outside the selected source
trial. Their presence preserves the source's one-time necklace reading. -/

open Set
open scoped Classical
namespace ExceptionalTimes.PairSquareSewing
open CenteredBlocks

variable {I : Type*}

noncomputable def overwriteSourceHistory (endpoint : I × Fin 2 ↪ Site)
    (ω : Configuration) (h : I → Bool → PairColor) : TwoTimeConfiguration :=
  fun t => overwriteDimers endpoint ω (fun i => h i t)

theorem overwriteSourceHistory_eqOn (endpoint : I × Fin 2 ↪ Site)
    (ω : Configuration) (h : I → Bool → PairColor) (S : Set Site)
    (havoid : ∀ i e, endpoint (i,e) ∉ S) (t : Bool) :
    Set.EqOn (overwriteSourceHistory endpoint ω h t) ω S := by
  intro v hv
  apply overwriteDimers_outside
  rintro ⟨⟨i,e⟩,rfl⟩
  exact havoid i e hv

theorem overwriteSourceHistory_congr (endpoint : I × Fin 2 ↪ Site)
    (ω η : Configuration) (h : I → Bool → PairColor) (S : Set Site)
    (heq : Set.EqOn ω η S) (t : Bool) :
    Set.EqOn (overwriteSourceHistory endpoint ω h t)
      (overwriteSourceHistory endpoint η h t) S := by
  intro v hv
  by_cases hr : v ∈ Set.range endpoint
  · obtain ⟨ie,rfl⟩ := hr
    simp only [overwriteSourceHistory,overwriteDimers_endpoint]
  · exact (overwriteDimers_outside endpoint ω _ hr).trans
      ((heq hv).trans (overwriteDimers_outside endpoint η _ hr).symm)

/-- A literal block change alters only the two sites of that block. -/
theorem overwriteSourceHistory_block_change (endpoint : I × Fin 2 ↪ Site)
    (ω : Configuration) (h : I → Bool → PairColor) (i : I) (a : Bool → PairColor)
    (P : Probe) (hinside : ∀ e, endpoint (i,e) ∈ P.pocket) (t : Bool) :
    Set.EqOn (overwriteSourceHistory endpoint ω (Function.update h i a) t)
      (overwriteSourceHistory endpoint ω h t) P.pocketᶜ := by
  intro v hv
  by_cases hr : v ∈ Set.range endpoint
  · obtain ⟨⟨j,e⟩,rfl⟩ := hr
    have hji : j≠i := by
      intro hj
      subst j
      exact hv (hinside e)
    simp only [overwriteSourceHistory,overwriteDimers_endpoint,Function.update_of_ne hji]
  · exact (overwriteDimers_outside endpoint ω _ hr).trans
      (overwriteDimers_outside endpoint ω _ hr).symm

/-- Both source quad-placement alternatives apply to arbitrary fixed
exterior annotations, whenever the actual screen and exterior agreements
are satisfied. -/
theorem source_reading_of_placed_relation (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {Q : Type*} (J : SourceSeamLayout) (quads : Q → GraphQuad)
    (ω : Sources Λ) (exterior : Bool) (inner : Bool → NecklaceShape)
    (outer : NecklaceShape) (background : Bool → TwoTimeConfiguration)
    (hrel : ∀ a, J.relation (inner a) outer (sewnField J.inside ω a exterior))
    (hbackground : ∀ a t, Set.EqOn (background a t)
      (complete (sewnField J.inside ω a exterior)) (J.support : Set Site))
    (hext : ∀ a b t, Set.EqOn (background a t) (background b t) outer.outsideSites)
    (hplace : J.QuadPlacement quads) :
    SourceOneTimeReading quads J.pocket inner background := by
  have hout := hplace.outer outer (hrel false).1.2.1
  intro q t a b ξ η hξ hη hbit
  rcases hout q with hd | hc
  · apply (quads q).test_congr
    intro v hv
    have hvout : v ∈ outer.outsideSites := Or.inl (hd v hv)
    have hvp : v ∉ J.pocket := by
      intro hp
      exact hd v hv ((hrel false).2.2.1 (J.pocket_inside hp))
    exact (hξ hvp).trans ((hext a b t hvout).trans (hη hvp).symm)
  · have hr := source_one_time_reading_of_relation hexInput J (fun _ : Unit => quads q)
      ω exterior inner outer background hrel hbackground hext
      (fun _ => hc.1) (fun _ => hc.2.1) (fun _ => hc.2.2)
    exact hr () t a b ξ η hξ hη hbit

/-- The source's literal successful seam continues to transmit the pair and
square when every other dimer history is overwritten at its actual endpoints
outside the screened trial. There is no new probabilistic assumption. -/
theorem source_success_transmitted_overwrite (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {QA QB : Type*} (J : SourceSeamLayout)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (D : Finset Site) (x z : Site) (ω : Sources Λ)
    (endpoint : I × Fin 2 ↪ Site) (history : I → Bool → PairColor)
    (havoid : ∀ i e, endpoint (i,e) ∉ J.inside ∧ endpoint (i,e) ∉ J.support)
    (hx : x ∈ J.pocket) (hz : x+z ∈ J.pocket) (hD : D ⊆ J.pocket)
    (hplaceA : J.QuadPlacement quadsA) (hplaceB : J.QuadPlacement quadsB)
    (hsuccess : J.success ω=true) :
    TransmittedAnnotations D x z
      (overwriteSourceHistory endpoint (complete ω.1) history) (fun _ => complete ω.2)
      (overwriteSourceHistory endpoint (complete (seamSwap J.inside ω).1) history)
      (fun _ => complete (seamSwap J.inside ω).2)
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  have hsuccess' : FourWaySuccess J.inside J.relation ω := of_decide_eq_true hsuccess
  obtain ⟨inner,outer,hrel⟩ := hsuccess'
  have hreadA : SourceOneTimeReading quadsA J.pocket inner
      (fun a => overwriteSourceHistory endpoint (complete (sewnField J.inside ω a false)) history) := by
    apply source_reading_of_placed_relation hexInput J quadsA ω false inner (outer false) _
      (fun a => hrel a false) _ _ hplaceA
    · intro a t
      exact overwriteSourceHistory_eqOn endpoint _ history (J.support : Set Site)
        (fun i e => (havoid i e).2) t
    · intro a b t
      apply overwriteSourceHistory_congr
      intro v hv
      have hvIn : v ∉ J.inside := by
        intro hin
        rcases hv with hv | hv
        · exact hv ((hrel false false).2.2.1 hin)
        · exact Finset.disjoint_left.mp (hrel false false).2.2.2 hv hin
      by_cases hvΛ : v ∈ Λ <;> simp [complete,sewnField,hvΛ,hvIn]
  have hreadB := source_sewn_reading hexInput J quadsB ω true inner (outer true)
    (fun a => hrel a true) hplaceB
  have hfreeze (a b t : Bool) : Set.EqOn
      (overwriteSourceHistory endpoint (complete (sewnField J.inside ω a b)) history t)
      (complete (if a then ω.2 else ω.1)) (inner a).insideSites := by
    apply (overwriteSourceHistory_eqOn endpoint _ history (inner a).insideSites _ t).trans
      (source_sewn_frozen J ω a b (inner a) (hrel a b).2.1)
    intro i e hv
    exact (havoid i e).1 ((hrel a b).2.1 hv)
  have hfreezeRaw (a b t : Bool) := source_sewn_frozen J ω a b (inner a) (hrel a b).2.1
  have hs0 : sewnField J.inside ω false false=ω.1 := by funext v; simp [sewnField]
  have hs1 : sewnField J.inside ω true true=ω.2 := by funext v; simp [sewnField]
  have hs10 : sewnField J.inside ω true false=(seamSwap J.inside ω).1 := rfl
  have hs01 : sewnField J.inside ω false true=(seamSwap J.inside ω).2 := rfl
  apply source_readings_transmitted quadsA quadsB outerA outerB J.pocket D x z hx hz hD
    inner (fun a => complete (if a then ω.2 else ω.1))
  · simpa only [hs0] using hfreeze false false
  · simpa only [hs1] using hfreezeRaw true true
  · simpa only [hs10] using hfreeze true false
  · simpa only [hs01] using hfreezeRaw false true
  · convert hreadA using 1
    funext a t
    cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,hs0,hs10]
  · convert hreadB using 1
    funext a t
    cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,hs1,hs01]

#print axioms overwriteSourceHistory_block_change
#print axioms source_success_transmitted_overwrite
end ExceptionalTimes.PairSquareSewing
