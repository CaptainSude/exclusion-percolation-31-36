import ExceptionalTimes.DimerBaseField
import ExceptionalTimes.SourceDimerDistinguished
import ExceptionalTimes.DimerJumpCalibration

/-! A single selected insertion is exactly the raw pair response under
the static fair field. This connects local calibration gadgets to the
degree-one coefficient used by the actual finite product expansion. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.DimerSingleton

open PairSquareSewing DimerLaw DimerExpansion DimerSelectedDictionary
open DimerBaseField CenteredBlocks BlockExpansion EnvironmentVariance ProbeProduct
open ActivePartitionLaw CanonicalSpatialProduct

noncomputable section
variable {B : Type*} [Fintype B]

omit [Fintype B] in
theorem singleton_kernel {H : Type*} [Fintype H] (b : B) (u : H → ℝ)
    (F : (({b} : Finset B) → H) → ℝ) :
    kernel (fun _ : ({b} : Finset B) => u) F=∑ a,u a*F (fun _ => a) := by
  let e : (({b} : Finset B) → H) ≃ H := {
    toFun := fun h => h ⟨b,by simp⟩
    invFun := fun a _ => a
    left_inv := by
      intro h
      funext j
      apply congrArg h
      apply Subtype.ext
      exact (Finset.mem_singleton.mp j.property).symm
    right_inv := fun _ => rfl }
  unfold kernel
  have he := e.symm.sum_comp (fun h => (∏ i : ({b} : Finset B),u (h i))*F h)
  calc
    _ = ∑ h : ({b} : Finset B) → H,(∏ i : ({b} : Finset B),u (h i))*F h := by
      apply Finset.sum_congr (by ext h; simp)
      intro h _
      rfl
    _ = ∑ a : H,(∏ i : ({b} : Finset B),u (e.symm a i))*F (e.symm a) := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      change (∏ _i : ({b} : Finset B),u a)*F (fun _ => a)=_
      simp

omit [Fintype B] in
theorem overwrite_singleton (slot : B×Fin 2 ↪ Site) (b : B)
    (ω : Configuration) (a : Color) (x z : Site)
    (h0 : slot (b,0)=x) (h1 : slot (b,1)=x+z) :
    overwriteDimers (selectedSlot slot {b}) ω (fun _ => a)=putPair ω x z (a 0) (a 1) := by
  have hx : x≠x+z := by
    intro h
    have he := congrArg Prod.snd (slot.injective (h0.trans (h.trans h1.symm)))
    norm_num at he
  funext v
  by_cases hr : v∈Set.range (selectedSlot slot {b})
  · obtain ⟨⟨j,e⟩,rfl⟩ := hr
    have hj : j.val=b := Finset.mem_singleton.mp j.property
    rw [overwriteDimers_endpoint]
    change a e=putPair ω x z (a 0) (a 1) (slot (j.val,e))
    rw [hj]
    fin_cases e <;> simp [putPair,h0,h1,hx]
  · have hv0 : v≠x := by
      intro h
      apply hr
      exact ⟨(⟨b,by simp⟩,0),h0.trans h.symm⟩
    have hv1 : v≠x+z := by
      intro h
      apply hr
      exact ⟨(⟨b,by simp⟩,1),h1.trans h.symm⟩
    rw [overwriteDimers_outside _ _ _ hr,putPair_outside _ _ _ _ _ _ hv0 hv1]

theorem selected_singleton_fair_raw (slot : B×Fin 2 ↪ Site)
    (D : Finset Site) (hcover : ∀ v∈D,∃ be,slot be=v)
    (b : B) (rule : Rule) (x z : Site)
    (h0 : slot (b,0)=x) (h1 : slot (b,1)=x+z)
    (F : TwoTimeConfiguration → ℝ)
    (hlocal : ∀ ω η : TwoTimeConfiguration,(∀ t v,v∈D → ω t v=η t v) → F ω=F η) :
    selectedKernel (fun _ : B => base)
      (fun _ h => rule.insertionWeight (historyEquiv h)) {b}
      (fun h => F (canonicalBackground slot (pairCoordinates.symm h)))=
      (fairSites D).expect (fun ω => rawPairResponse rule.kernel (fun _ => complete ω) x z F) := by
  rw [selected_coefficient_fair_overwrites slot D hcover _ {b} F hlocal]
  apply FiniteLaw.expect_congr
  intro ω
  simp only [Equiv.apply_symm_apply]
  rw [singleton_kernel]
  rw [←rule.insertionWeight_eq_raw (fun _ => complete ω) x z F]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  congr 1
  apply congrArg F
  funext t
  cases t <;> exact overwrite_singleton slot b (complete ω) _ x z h0 h1

theorem jumpTest_local (Q : PolygonQuad) :
    ∀ ω η : TwoTimeConfiguration,
      (∀ t v,v∈Q.support → ω t v=η t v) →
        DimerJumpCalibration.jumpTest Q ω=DimerJumpCalibration.jumpTest Q η := by
  intro ω η he
  have h0 := Q.test_congr (a := ω false) (b := η false) (he false)
  have h1 := Q.test_congr (a := ω true) (b := η true) (he true)
  simp only [DimerJumpCalibration.jumpTest,h0,h1]

theorem canonical_singleton_jump (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad)
    (hcover : ∀ v∈Q.support,∃ be,slot be=v) (b : B) (x z : Site)
    (h0 : slot (b,0)=x) (h1 : slot (b,1)=x+z) :
    selectedKernel (fun _ : B => base) (fun _ => canonicalInsertion) {b}
      (fun h => DimerJumpCalibration.jumpTest Q (canonicalBackground slot (pairCoordinates.symm h)))=
      (fairSites Q.support).expect (fun ω =>
        rawPairResponse Rule.canonical.kernel (fun _ => complete ω) x z
          (DimerJumpCalibration.jumpTest Q)) := by
  exact selected_singleton_fair_raw slot Q.support hcover b .canonical x z h0 h1
    (DimerJumpCalibration.jumpTest Q) (jumpTest_local Q)

theorem refresh_singleton_jump (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad)
    (hcover : ∀ v∈Q.support,∃ be,slot be=v) (b : B) (x z : Site)
    (h0 : slot (b,0)=x) (h1 : slot (b,1)=x+z) :
    selectedKernel (fun _ : B => base) (fun _ => refreshInsertion) {b}
      (fun h => DimerJumpCalibration.jumpTest Q (canonicalBackground slot (pairCoordinates.symm h)))=
      (fairSites Q.support).expect (fun ω =>
        rawPairResponse Rule.refresh.kernel (fun _ => complete ω) x z
          (DimerJumpCalibration.jumpTest Q)) := by
  exact selected_singleton_fair_raw slot Q.support hcover b .refresh x z h0 h1
    (DimerJumpCalibration.jumpTest Q) (jumpTest_local Q)

#print axioms selected_singleton_fair_raw

end
end ExceptionalTimes.DimerSingleton


