import ExceptionalTimes.DimerPivotalCalibration

/-! The endpoint-refresh degree-one clock is exactly one quarter of the
literal expected number of pivotal sites of the reference polygon. Extra
sites in a finite matching cover contribute zero. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.DimerPivotalCount

open PairSquareSewing DimerLaw DimerExpansion DimerSelectedDictionary DimerBaseField
open DimerSingleton DimerJumpCalibration DimerPivotalCalibration BlockExpansion EnvironmentVariance
open ProbeProduct ActivePartitionLaw CanonicalSpatialProduct FiniteHaar IndependentAnnulusInput

noncomputable section
variable {B : Type*} [Fintype B]

omit [Fintype B] in
theorem pairDecode_update_endpoint (slot : B×Fin 2 ↪ Site) (x : B → Color)
    (b : B) (e : Fin 2) (a : Bool) :
    pairDecode slot (Function.update x b (Function.update (x b) e a))=
      force {slot (b,e)} (pairDecode slot x) a := by
  funext v
  by_cases hv : v∈Set.range slot
  · obtain ⟨⟨j,d⟩,rfl⟩ := hv
    rw [pairDecode_at]
    have hs : slot (j,d)=slot (b,e) ↔ j=b ∧ d=e := by
      rw [slot.injective.eq_iff,Prod.mk.injEq]
    by_cases hj : j=b
    · subst j
      by_cases hd : d=e
      · subst d; simp [force]
      · simp [force,hs,hd,pairDecode_at]
    · simp [force,hs,hj,pairDecode_at]
  · have hv' : v≠slot (b,e) := fun h => hv ⟨(b,e),h.symm⟩
    rw [pairDecode_off slot _ hv]
    simp [force,hv',pairDecode_off slot x hv]

omit [Fintype B] in
theorem pivotal_at_slot (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad)
    (x : B → Color) (b : B) (e : Fin 2) :
    pivotal (fun y => Q.test (pairDecode slot y)) b e x=
      indicator (IsPivotal Q (slot (b,e)) (pairDecode slot x)) := by
  unfold pivotal IsPivotal
  dsimp only
  rw [pairDecode_update_endpoint,pairDecode_update_endpoint]

theorem pivotal_off_support (Q : PolygonQuad) (ω : Configuration) (v : Site)
    (hv : v∉Q.support) : indicator (IsPivotal Q v ω)=0 := by
  have he : Q.test (force {v} ω false)=Q.test (force {v} ω true) := by
    apply Q.test_congr
    intro w hw
    have hne : w≠v := fun h => hv (h ▸ hw)
    simp [force,hne]
  simp [indicator,IsPivotal,he]

theorem pivotal_congr (Q : PolygonQuad) (v : Site) (ω η : Configuration)
    (he : ∀ w∈Q.support,ω w=η w) :
    indicator (IsPivotal Q v ω)=indicator (IsPivotal Q v η) := by
  have hh (a : Bool) : Q.test (force {v} ω a)=Q.test (force {v} η a) := by
    apply Q.test_congr
    intro w hw
    by_cases h : w=v
    · subst w; simp [force]
    · simp [force,h,he w hw]
  simp only [IsPivotal,hh]

theorem sum_slots_pivotal (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad)
    (hcover : ∀ v∈Q.support,∃ be,slot be=v) (ω : Configuration) :
    (∑ b : B,∑ e : Fin 2,indicator (IsPivotal Q (slot (b,e)) ω))=
      ∑ v∈Q.support,indicator (IsPivotal Q v ω) := by
  rw [←Fintype.sum_prod_type (fun be : B×Fin 2 => indicator (IsPivotal Q (slot be) ω))]
  have hsub : Q.support⊆(Finset.univ : Finset (B×Fin 2)).map slot := by
    intro v hv
    obtain ⟨be,hbe⟩ := hcover v hv
    exact Finset.mem_map.mpr ⟨be,Finset.mem_univ _,hbe⟩
  calc
    _ = ∑ v∈(Finset.univ : Finset (B×Fin 2)).map slot,indicator (IsPivotal Q v ω) := by
      rw [Finset.sum_map]
    _ = _ := (Finset.sum_subset hsub (fun v _ hv => pivotal_off_support Q ω v hv)).symm

theorem refreshJump_eq_pivotal (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad)
    (hcover : ∀ v∈Q.support,∃ be,slot be=v) :
    4*refreshJump slot Q=
      (fairSites Q.support).expect (fun ω =>
        ∑ v∈Q.support,indicator (IsPivotal Q v (complete ω))) := by
  rw [refreshJump_eq_sum]
  have hs (b : B) :
      selectedKernel (fun _ : B => base) (fun _ => refreshInsertion) {b}
        (fun h => jumpTest Q (canonicalBackground slot (pairCoordinates.symm h)))=
      (1/4:ℝ)*average (fun x => ∑ e,pivotal (fun y => Q.test (pairDecode slot y)) b e x) :=
    singleton_refresh_pivotal b (fun y => Q.test (pairDecode slot y))
  simp_rw [hs]
  rw [←Finset.mul_sum,←average_sum]
  have hc : (4:ℝ)*(1/4)=1 := by norm_num
  rw [←mul_assoc,hc,one_mul]
  simp_rw [pivotal_at_slot,sum_slots_pivotal slot Q hcover]
  rw [FiniteSiteLaw.average_pairDecode slot
    (fun ω => ∑ v∈Q.support,indicator (IsPivotal Q v ω))]
  apply FiniteSiteLaw.average_site_embedding slot Q.support hcover
    (fun ω => ∑ v∈Q.support,indicator (IsPivotal Q v ω))
  intro ω η he
  apply Finset.sum_congr rfl
  intro v _
  exact pivotal_congr Q v ω η he

theorem four_refreshJump_eq_pivotalMean (n : ℕ) (slot : B×Fin 2 ↪ Site)
    (hcover : ∀ v∈(reference n).support,∃ be,slot be=v) :
    4*refreshJump slot (reference n)=pivotalMean n :=
  refreshJump_eq_pivotal slot (reference n) hcover

theorem independent_clock_identity (n : ℕ) (slot : B×Fin 2 ↪ Site)
    (hcover : ∀ v∈(reference n).support,∃ be,slot be=v) (T : ℝ) :
    (T/(2*refreshJump slot (reference n)))/2=T/pivotalMean n := by
  rw [←four_refreshJump_eq_pivotalMean n slot hcover]
  ring

#print axioms four_refreshJump_eq_pivotalMean
#print axioms independent_clock_identity

end
end ExceptionalTimes.DimerPivotalCount
