import ExceptionalTimes.WiredPivotal
import ExceptionalTimes.FiniteMatchingClosure

/-! Exact middle-annulus support and restriction. The support includes
the one-step exiting layer, which must be covered by active whole dimers. -/

namespace ExceptionalTimes.HoleFilling

def annularSites (r R : ℕ) : Finset Site := latticeBox (R+1) \ latticeBox r

theorem fillBox_graph_mono (ω : Configuration) {r s : ℕ} (hrs : r ≤ s) :
    blackGraph (fillBox ω r) ≤ blackGraph (fillBox ω s) := by
  apply blackGraph_mono
  intro z hz
  by_cases hzs : z ∈ latticeBox s
  · exact fillBox_inside ω s hzs
  have hzr : z ∉ latticeBox r := fun h => hzs (latticeBox_mono hrs h)
  simpa only [fillBox_outside ω r hzr,fillBox_outside ω s hzs] using hz

/-- A larger-hole, smaller-outer-radius event follows from the original
radial event, with the original colors at all exiting vertices retained. -/
theorem wiredArm_restrict (ω : Configuration) {r s S R : ℕ}
    (hrs : r ≤ s) (hsS : s ≤ S) (hSR : S ≤ R)
    (h : WiredArm ω r R) : WiredArm ω s S := by
  obtain ⟨w,hw,hwR⟩ := (oneArm_fillBox_iff_wiredArm ω (hrs.trans (hsS.trans hSR))).mpr h
  apply (oneArm_fillBox_iff_wiredArm ω hsS).mp
  refine ⟨w,⟨fillBox_inside ω s (origin_mem_box s),
    hw.2.mono (fillBox_graph_mono ω hrs)⟩,?_⟩
  exact fun hwS => hwR (latticeBox_mono hSR hwS)

theorem wiredArmTest_congr_annularSites {r R : ℕ} (hrR : r ≤ R)
    (ω η : Configuration) (heq : ∀ v ∈ annularSites r R, ω v = η v) :
    wiredArmTest r R ω = wiredArmTest r R η := by
  unfold wiredArmTest
  apply decide_eq_decide.mpr
  apply wiredArm_congr_on_annulus ω η hrR
  intro v hvR hvr
  exact heq v (Finset.mem_sdiff.mpr ⟨hvR,hvr⟩)

theorem wiredArmTest_eq_wiredPivotal (r R : ℕ) :
    wiredArmTest r R = WiredPivotal.wiredArmTest r R := by
  funext ω
  by_cases h : WiredArm ω r R <;> simp [wiredArmTest,WiredPivotal.wiredArmTest,h]

theorem annularSites_mono {r s S R : ℕ} (hrs : r ≤ s) (hSR : S ≤ R) :
    annularSites s S ⊆ annularSites r R := by
  intro v hv
  obtain ⟨hvS,hvs⟩ := Finset.mem_sdiff.mp hv
  apply Finset.mem_sdiff.mpr
  exact ⟨latticeBox_mono (Nat.add_le_add_right hSR 1) hvS,
    fun hvr => hvs (latticeBox_mono hrs hvr)⟩

theorem partner_mem_enlarged_box (z : Site) {d R : ℕ} (hz : z ∈ latticeBox d)
    {v : Site} (hv : v ∈ latticeBox R) :
    PeriodicMatching.partner z v ∈ latticeBox (R+d) := by
  rcases PeriodicMatching.partner_displacement z v with he | he
  all_goals rw [he]
  all_goals simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
    PeriodicMatching.add,PeriodicMatching.sub] at hz hv ⊢
  all_goals omega

theorem partner_not_mem_smaller_box (z : Site) (hz0 : z ≠ (0,0))
    {d r : ℕ} (hz : z ∈ latticeBox d) (hdr : d ≤ r)
    {v : Site} (hv : v ∉ latticeBox r) :
    PeriodicMatching.partner z v ∉ latticeBox (r-d) := by
  intro hp
  have h := partner_mem_enlarged_box z hz hp
  rw [PeriodicMatching.partner_involutive z hz0] at h
  exact hv (by simpa [Nat.sub_add_cancel hdr] using h)

/-- Completing the middle event's support to whole dimers expands its
outer radius and contracts its hole by at most the displacement bound.
This proves an explicit active-collar margin, not merely finiteness. -/
theorem matchingClosure_annularSites_subset (z : Site) (hz0 : z ≠ (0,0))
    {d r R : ℕ} (hz : z ∈ latticeBox d) (hdr : d ≤ r) :
    FiniteMatchingClosure.closure (PeriodicMatching.partner z)
      (annularSites r R) ⊆ annularSites (r-d) (R+d) := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact annularSites_mono (Nat.sub_le r d) (Nat.le_add_right R d) hv
  · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨huR,hur⟩ := Finset.mem_sdiff.mp hu
    apply Finset.mem_sdiff.mpr
    exact ⟨by simpa [Nat.add_right_comm R 1 d] using partner_mem_enlarged_box z hz huR,
      partner_not_mem_smaller_box z hz0 hz hdr hur⟩

#print axioms wiredArm_restrict
#print axioms wiredArmTest_congr_annularSites
#print axioms matchingClosure_annularSites_subset

end ExceptionalTimes.HoleFilling

