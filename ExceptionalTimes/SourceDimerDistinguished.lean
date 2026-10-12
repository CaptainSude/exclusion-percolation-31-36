import ExceptionalTimes.SourceSeamFull

/-! Exact extraction of one distinguished dimer insertion from the full
centered history kernel. No geometric or probabilistic estimate is used. -/

open Set
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.PairSquareSewing
open DimerBinaryResponse EnvironmentVariance CenteredBlocks

/-- Bool-indexed histories and the exact expansion's pair of colors. -/
def insertionHistoryEquiv : (Bool → PairColor) ≃ DimerExpansion.History where
  toFun h := (h false,h true)
  invFun h t := if t then h.2 else h.1
  left_inv h := by funext t; cases t <;> rfl
  right_inv _ := rfl

noncomputable def Rule.insertionWeight (rule : Rule) (h : Bool → PairColor) : ℝ :=
  match rule with
  | .canonical => DimerExpansion.canonicalInsertion (insertionHistoryEquiv h)
  | .refresh => DimerExpansion.refreshInsertion (insertionHistoryEquiv h)

theorem Rule.insertionWeight_centered (rule : Rule) : ∑ h, rule.insertionWeight h=0 := by
  cases rule
  · exact (insertionHistoryEquiv.sum_comp DimerExpansion.canonicalInsertion).trans
      DimerExpansion.canonicalInsertion_centered
  · exact (insertionHistoryEquiv.sum_comp DimerExpansion.refreshInsertion).trans
      DimerExpansion.refreshInsertion_centered

theorem Rule.insertionWeight_variation (rule : Rule) :
    variation rule.insertionWeight=if rule=Rule.canonical then 1/2 else 1 := by
  cases rule
  · change (∑ h, |DimerExpansion.canonicalInsertion (insertionHistoryEquiv h)|)=_
    rw [insertionHistoryEquiv.sum_comp (fun h => |DimerExpansion.canonicalInsertion h|)]
    simpa only [ite_true,variation] using DimerExpansion.canonicalInsertion_variation
  · change (∑ h, |DimerExpansion.refreshInsertion (insertionHistoryEquiv h)|)=_
    rw [insertionHistoryEquiv.sum_comp (fun h => |DimerExpansion.refreshInsertion h|)]
    simpa only [reduceCtorEq,ite_false,variation] using DimerExpansion.refreshInsertion_variation

theorem Rule.insertionWeight_variation_le_one (rule : Rule) :
    variation rule.insertionWeight≤1 := by
  rw [Rule.insertionWeight_variation]
  split <;> norm_num

theorem Rule.insertionWeight_eq_raw (rule : Rule) (background : TwoTimeConfiguration)
    (x z : Site) (F : TwoTimeConfiguration → ℝ) :
    (∑ h : Bool → PairColor, rule.insertionWeight h *
      F (pairHistory background x z (h false 0,h false 1) (h true 0,h true 1))) =
      rawPairResponse rule.kernel background x z F := by
  have he := insertionHistoryEquiv.symm.sum_comp
    (fun h : Bool → PairColor => rule.insertionWeight h *
      F (pairHistory background x z (h false 0,h false 1) (h true 0,h true 1)))
  rw [←he]
  cases rule
  · exact canonical_weight_eq_raw background x z F
  · exact refresh_weight_eq_raw background x z F

variable {I : Type*}
noncomputable local instance : DecidableEq I := Classical.decEq _

def otherEndpoint (endpoint : I × Fin 2 ↪ Site) (i : I) : {j // j≠i} × Fin 2 ↪ Site where
  toFun je := endpoint (je.1.val,je.2)
  inj' := by
    rintro ⟨j,e⟩ ⟨k,f⟩ h
    have hh := endpoint.injective h
    have hjk : j=k := Subtype.ext (congrArg Prod.fst hh)
    have hef : e=f := congrArg (fun p : I × Fin 2 => p.2) hh
    exact Prod.ext hjk hef

/-- Every actual simultaneous overwrite is the distinguished pair
written over the remaining actual endpoint overwrites. -/
theorem overwriteDimers_distinguished (endpoint : I × Fin 2 ↪ Site) (i : I)
    (ω : Configuration) (color : I → PairColor) (x z : Site)
    (h0 : endpoint (i,0)=x) (h1 : endpoint (i,1)=x+z) :
    overwriteDimers endpoint ω color =
      putPair (overwriteDimers (otherEndpoint endpoint i) ω (fun j => color j))
        x z (color i 0) (color i 1) := by
  have hxz : x≠x+z := by
    intro h
    have he := congrArg Prod.snd (endpoint.injective (h0.trans (h.trans h1.symm)))
    norm_num at he
  funext v
  by_cases hr : v∈Set.range endpoint
  · obtain ⟨⟨j,e⟩,rfl⟩ := hr
    rw [overwriteDimers_endpoint]
    by_cases hj : j=i
    · subst j
      fin_cases e <;> simp [putPair,h0,h1,hxz]
    · have hv0 : endpoint (j,e)≠x := by
        intro h
        exact hj (congrArg Prod.fst (endpoint.injective (h.trans h0.symm)))
      have hv1 : endpoint (j,e)≠x+z := by
        intro h
        exact hj (congrArg Prod.fst (endpoint.injective (h.trans h1.symm)))
      rw [putPair_outside _ x z _ _ _ hv0 hv1]
      exact (overwriteDimers_endpoint (otherEndpoint endpoint i) ω (fun j => color j)
        (⟨j,hj⟩,e)).symm
  · have hv0 : v≠x := fun h => hr ⟨(i,0),h0.trans h.symm⟩
    have hv1 : v≠x+z := fun h => hr ⟨(i,1),h1.trans h.symm⟩
    have hro : v∉Set.range (otherEndpoint endpoint i) := by
      rintro ⟨⟨j,e⟩,h⟩
      exact hr ⟨(j.val,e),h⟩
    rw [overwriteDimers_outside _ _ _ hr,putPair_outside _ x z _ _ _ hv0 hv1,
      overwriteDimers_outside _ _ _ hro]

theorem overwriteSourceHistory_distinguished (endpoint : I × Fin 2 ↪ Site) (i : I)
    (ω : Configuration) (history : I → Bool → PairColor) (x z : Site)
    (h0 : endpoint (i,0)=x) (h1 : endpoint (i,1)=x+z) :
    overwriteSourceHistory endpoint ω history =
      pairHistory (overwriteSourceHistory (otherEndpoint endpoint i) ω (fun j => history j))
        x z (history i false 0,history i false 1) (history i true 0,history i true 1) := by
  funext t
  have hh := overwriteDimers_distinguished endpoint i ω (fun j => history j t) x z h0 h1
  cases t <;> exact hh

variable [Fintype I]

/-- The full signed kernel is the remaining centered kernel applied to
the literal two-site response, without absolute values or union bounds. -/
theorem centered_kernel_distinguished (endpoint : I × Fin 2 ↪ Site) (i : I)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule)
    (hw : w i=rule.insertionWeight) (ω : Configuration) (x z : Site)
    (h0 : endpoint (i,0)=x) (h1 : endpoint (i,1)=x+z)
    (F : TwoTimeConfiguration → ℝ) :
    kernel w (fun history => F (overwriteSourceHistory endpoint ω history)) =
      multiPairResponse (fun j : {j // j≠i} => w j) rule.kernel
        (overwriteSourceHistory (otherEndpoint endpoint i) ω) x z F := by
  rw [kernel_split w _ i]
  dsimp only [multiPairResponse,kernel]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  apply congrArg (fun r : ℝ => (∏ j : {j // j≠i}, w j (h j))*r)
  rw [hw,←Rule.insertionWeight_eq_raw rule
    (overwriteSourceHistory (otherEndpoint endpoint i) ω h) x z F]
  apply Finset.sum_congr (by ext a; simp)
  intro a _
  apply congrArg (fun r : ℝ => rule.insertionWeight a*r)
  apply congrArg F
  rw [overwriteSourceHistory_distinguished endpoint i ω _ x z h0 h1]
  have hfirst : (Equiv.piSplitAt i (fun _ : I => Bool → PairColor)).symm (a,h) i=a := by
    simp [Equiv.piSplitAt]
  have hother : (fun j : {j // j≠i} =>
      (Equiv.piSplitAt i (fun _ : I => Bool → PairColor)).symm (a,h) j)=h := by
    funext j
    simp [Equiv.piSplitAt,j.property]
  rw [hfirst,hother]

/-- The same identity under the actual finite iid fair background is
exactly the averaged multi-pair coefficient used by source sewing. -/
theorem averaged_centered_kernel_distinguished (Λ : Finset Site)
    (endpoint : I × Fin 2 ↪ Site) (i : I)
    (w : I → (Bool → PairColor) → ℝ) (rule : Rule)
    (hw : w i=rule.insertionWeight) (x z : Site)
    (h0 : endpoint (i,0)=x) (h1 : endpoint (i,1)=x+z)
    (F : TwoTimeConfiguration → ℝ) :
    (ProbeProduct.fairSites ↥Λ).expect (fun ω =>
      kernel w (fun history => F (overwriteSourceHistory endpoint (complete ω) history))) =
      averagedMultiPairResponse Λ (fun j : {j // j≠i} => w j) rule
        (otherEndpoint endpoint i) x z F := by
  apply FiniteLaw.expect_congr
  intro ω
  exact centered_kernel_distinguished endpoint i w rule hw (complete ω) x z h0 h1 F

#print axioms Rule.insertionWeight_centered
#print axioms Rule.insertionWeight_variation
#print axioms overwriteDimers_distinguished
#print axioms centered_kernel_distinguished
#print axioms averaged_centered_kernel_distinguished
end ExceptionalTimes.PairSquareSewing
