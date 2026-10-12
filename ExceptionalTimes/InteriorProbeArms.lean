import ExceptionalTimes.StraightBoxMixedNecessity
import ExceptionalTimes.MixedBoundaryBound

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ArmEnlargement

noncomputable def Probe.inset (P : Probe) (h : 16*P.innerRadius<P.outerRadius) : Probe where
  mesh := P.mesh
  center := P.center
  innerRadius := P.innerRadius
  outerRadius := P.outerRadius/4
  mesh_pos := P.mesh_pos
  inner_pos := P.inner_pos
  radii := by linarith

def InteriorProbeArms (P : Probe) (ω : Configuration) : Prop :=
  ∀ h : 16*P.innerRadius<P.outerRadius, FourArms (P.inset h) ω

theorem Probe.inset_region (P : Probe) (h : 16*P.innerRadius<P.outerRadius) :
    (P.inset h).region ⊆ P.region := by
  intro v hv
  change P.innerRadius/2≤P.radius v ∧ P.radius v≤2*(P.outerRadius/4) at hv
  exact ⟨hv.1,by linarith [hv.2,P.inner_pos]⟩

theorem inset_inside_of_no_contact (P : Probe) (n : ℕ)
    (hv : ∃ v ∈ latticeBox n, v ∈ P.pocket)
    (hno : ∀ s, ¬SideContact P.mesh n P.outerRadius (HexCells.center P.center) s)
    (h : 16*P.innerRadius<P.outerRadius) :
    Metric.closedBall (position P.mesh P.center) (2*(P.inset h).outerRadius) ⊆
      physicalHomeomorph (P.inset h) '' interior (axialRectangle n) := by
  intro z hz
  let p := (physicalHomeomorph (P.inset h)).symm z
  have hpz : physicalHomeomorph (P.inset h) p=z := (physicalHomeomorph (P.inset h)).apply_symm_apply z
  refine ⟨p,interior_rectangle_of_slacks n p ?_,hpz⟩
  intro s
  have hc := inward_slack_of_pocket P n s hv (hno s)
  have hd := boxSideSlack_dist P.mesh_pos.le n s p (HexCells.center P.center)
  have hlo := mul_le_mul_of_nonneg_left
    (neg_le_abs (boxSideSlack n p s-boxSideSlack n (HexCells.center P.center) s)) P.mesh_pos.le
  have hpz' : axialPhysical P.mesh p=z := hpz
  rw [hpz'] at hd
  have hz' : dist z (axialPhysical P.mesh (HexCells.center P.center))≤2*(P.outerRadius/4) := hz
  have hpos : 0<P.mesh*boxSideSlack n p s := by linarith [P.inner_pos]
  exact (mul_pos_iff_of_pos_left P.mesh_pos).mp hpos

/-- A crossing change and absence of every side contact force the actual
inset bulk event. An empty inset is handled as the certain event. -/
theorem interiorProbeArms_of_no_contact (hsource : PublishedPolygonBulkArms)
    (n : ℕ) (hn : 0<n) (P : Probe) (he : 16*P.mesh<P.innerRadius)
    (hno : ∀ s, ¬SideContact P.mesh n P.outerRadius (HexCells.center P.center) s)
    (ω a b : Configuration) (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (ha : EqOn a ω P.region) (hb : EqOn b ω P.region)
    (hc : (axialBoxQuad n).test a ≠ (axialBoxQuad n).test b) : InteriorProbeArms P ω := by
  intro h
  have hv : ∃ v ∈ latticeBox n, v ∈ P.pocket := (axialBoxQuad n).changed_pocket P hab hc
  exact straightBox_localChangeArms_of_published hsource n hn (P.inset h) he
    (inset_inside_of_no_contact P n hv hno h) ω a b hab
    (ha.mono (P.inset_region h)) (hb.mono (P.inset_region h)) hc

theorem interior_probability_le_profile
    {B₀ C₄ C Q g : ℝ} (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α) (P : Probe) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh≤P.innerRadius)
    (hg : 0≤g) (hC : 1≤C) (hC₄ : 0≤C₄) (hK : 1≤C₄*Q)
    (hp : ∀ t, 0<t → t≤P.outerRadius → 0<p t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤Q*(p a/p b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → p b≤C*(b/a)^g*p a) :
    probability (fairSites D) (fun ω => InteriorProbeArms P (completeColors D ω)) ≤
      ((C₄*Q)*C^2*(16:ℝ)^g)*(p P.innerRadius/p P.outerRadius) := by
  have hr := P.inner_pos
  have hR : 0<P.outerRadius := by linarith [P.radii]
  have hrR : P.innerRadius≤P.outerRadius := by linarith [P.radii]
  have hpr := hp P.innerRadius hr hrR
  have hpR := hp P.outerRadius hR le_rfl
  have hC0 : 0≤C := by linarith
  have hK0 : 0≤C₄*Q := by linarith
  by_cases h : 16*P.innerRadius<P.outerRadius
  · have heq : probability (fairSites D) (fun ω => InteriorProbeArms P (completeColors D ω)) =
        probability (fairSites D) (fun ω => FourArms (P.inset h) (completeColors D ω)) := by
      apply probability_congr
      exact fun _ => ⟨fun h' => h' h,fun h' _ => h'⟩
    rw [heq]
    have hab : P.innerRadius<P.outerRadius/4 := by linarith
    have hbR : P.outerRadius/4≤P.outerRadius := by linarith
    have hstat := hfour (P.inset h) D hmesh ((P.inset_region h).trans hD)
    have hstat' : probability (fairSites D) (fun ω => FourArms (P.inset h) (completeColors D ω)) ≤
        (C₄*Q)*(p P.innerRadius/p (P.outerRadius/4)) := by
      apply hstat.trans
      have ht := mul_le_mul_of_nonneg_left (hquasi _ _ hr hab hbR) hC₄
      change C₄*α P.innerRadius (P.outerRadius/4)≤_
      convert ht using 1
      ring
    have hb0 : 0<P.outerRadius/4 := by positivity
    have hratio := ratio_compare p hr le_rfl hab.le hbR le_rfl hC0 hpr.le (hp _ hb0 hbR) hpR hlower
    have hscale : (P.innerRadius/P.innerRadius)*(P.outerRadius/(P.outerRadius/4))=4 := by
      field_simp
    rw [hscale] at hratio
    have hpow := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤4) (by norm_num : (4:ℝ)≤16) hg
    have hbound : p P.innerRadius/p (P.outerRadius/4)≤C^2*(16:ℝ)^g*(p P.innerRadius/p P.outerRadius) := by
      have hr' : p P.innerRadius/p (P.outerRadius/4)≤C^2*(4:ℝ)^g*(p P.innerRadius/p P.outerRadius) := by
        convert hratio using 1
        ring
      exact hr'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg C)) (div_nonneg hpr.le hpR.le))
    have ht := mul_le_mul_of_nonneg_left hbound hK0
    apply hstat'.trans
    convert ht using 1
    ring
  · have heq : probability (fairSites D) (fun ω => InteriorProbeArms P (completeColors D ω))=1 := by
      have he : ∀ ω, InteriorProbeArms P (completeColors D ω)↔True :=
        fun _ => ⟨fun _ => trivial,fun _ hh => (h hh).elim⟩
      rw [probability_congr (fairSites D) he]
      simp [probability,EnvironmentVariance.indicator,FiniteLaw.expect_const]
    rw [heq]
    have hscale : P.outerRadius/P.innerRadius≤16 := (div_le_iff₀ hr).mpr (le_of_not_gt h)
    have hpow := Real.rpow_le_rpow (div_nonneg hR.le hr.le) hscale hg
    have hCC : C≤(C₄*Q)*C^2 := by
      have h2 : C≤C^2 := by nlinarith
      have hk := mul_le_mul_of_nonneg_right hK (sq_nonneg C)
      linarith
    have hlarge : p P.outerRadius≤((C₄*Q)*C^2*(16:ℝ)^g)*p P.innerRadius := by
      calc
        _ ≤ C*(P.outerRadius/P.innerRadius)^g*p P.innerRadius := hlower _ _ hr hrR le_rfl
        _ ≤ C*(16:ℝ)^g*p P.innerRadius := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0) hpr.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (by norm_num) g)) hpr.le
    have ht := div_le_div_of_nonneg_right hlarge hpR.le
    rw [div_self (ne_of_gt hpR)] at ht
    convert ht using 1
    ring

#print axioms interiorProbeArms_of_no_contact
#print axioms interior_probability_le_profile

end ExceptionalTimes.PairSquareSewing
