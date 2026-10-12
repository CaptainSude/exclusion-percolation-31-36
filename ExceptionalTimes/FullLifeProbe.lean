import ExceptionalTimes.InteriorProbeArms

/-! A single deterministic arm event for every literal forest probe:
use the unique contacted side when one exists, and an inset bulk probe
otherwise. Necessity and the one-probe static bound are both proved. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct

def HasSideContact (n : ℕ) (P : Probe) : Prop :=
  ∃ s, SideContact P.mesh n P.outerRadius (HexCells.center P.center) s

noncomputable def StraightProbeArms (n : ℕ) (P : Probe) (ω : Configuration) : Prop :=
  if h : HasSideContact n P then
    MixedBoundaryArms P (boxHalfPlane n h.choose)
      (boxSideProjection n h.choose (HexCells.center P.center))
      (boxSideProjection_boundary n h.choose (HexCells.center P.center)) ω
  else InteriorProbeArms P ω

/-- Every local crossing change at a positive life forces the chosen
actual arm event. Four fixed corner roots rule out the two-side case. -/
theorem life_straightProbeArms {V : Type*} [Fintype V]
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (fixed : V → Prop) (anchor : V → ℂ) {cutoff stop : ℝ}
    (hcut : 0<cutoff) (n : ℕ) (hn : 0<n) (P : Probe)
    (hscale : 3*(stop/8)<P.mesh*n)
    (corner : Bool → Bool → V) (hfixed : ∀ s t, fixed (corner s t))
    (hcorner : ∀ s t, anchor (corner s t)=
      axialPhysical P.mesh (signedSide n s,signedSide n t))
    (life : ForestArmProbability.Life fixed anchor cutoff stop)
    (hcenter : anchor (ForestArmProbability.center fixed anchor cutoff stop life)=position P.mesh P.center)
    (houter : P.outerRadius=KruskalLives.death fixed anchor cutoff stop life.val/8)
    (he : 16*P.mesh<P.innerRadius)
    (ω a b : Configuration) (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (ha : EqOn a ω P.region) (hb : EqOn b ω P.region)
    (hc : (axialBoxQuad n).test a ≠ (axialBoxQuad n).test b) : StraightProbeArms n P ω := by
  by_cases h : HasSideContact n P
  · rw [StraightProbeArms,dite_eq_left h]
    exact life_mixedBoundaryArms_of_contact hbulkSource hhalfSource fixed anchor hcut n hn P
      hscale corner hfixed hcorner life hcenter houter h.choose he h.choose_spec ω a b hab ha hb hc
  · rw [StraightProbeArms,dite_eq_right h]
    exact interiorProbeArms_of_no_contact hbulkSource n hn P he
      (fun s hs => h ⟨s,hs⟩) ω a b hab ha hb hc

theorem FourArms.locality (P : Probe) {ω η : Configuration}
    (heq : EqOn ω η P.region) : FourArms P ω ↔ FourArms P η := fourArms_eqOn heq

theorem MixedBoundaryArms.locality (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) {ω η : Configuration} (heq : EqOn ω η P.region) :
    MixedBoundaryArms P H q hq ω ↔ MixedBoundaryArms P H q hq η := by
  constructor
  · intro h
    exact ⟨fun hb => (h.1 hb).mono_eqOn (heq.mono (P.bulkPart_region q hb)),
      fun hh => (h.2 hh).mono_eqOn (heq.mono (P.halfPart_region H q hq hh))⟩
  · intro h
    exact ⟨fun hb => (h.1 hb).mono_eqOn (heq.symm.mono (P.bulkPart_region q hb)),
      fun hh => (h.2 hh).mono_eqOn (heq.symm.mono (P.halfPart_region H q hq hh))⟩

theorem straightProbeArms_locality (n : ℕ) (P : Probe) {ω η : Configuration}
    (heq : EqOn ω η P.region) : StraightProbeArms n P ω ↔ StraightProbeArms n P η := by
  by_cases h : HasSideContact n P
  · simp only [StraightProbeArms,dite_eq_left h]
    exact MixedBoundaryArms.locality P _ _ _ heq
  · simp only [StraightProbeArms,dite_eq_right h,InteriorProbeArms]
    exact forall_congr' (fun ht => fourArms_eqOn (heq.mono (P.inset_region ht)))

noncomputable def fullProbeConstant (C₄ C₃ c C Q g : ℝ) : ℝ :=
  (C₄*Q)*(C₃*Q/c)*C^3*(8192:ℝ)^g + (C₄*Q)*C^2*(16:ℝ)^g

/-- This is a one-life probability bound for the explicit selected event,
under the original normalized finite iid fair coloring. Its hypotheses
are individual published static arm estimates and their stated profiles. -/
theorem straightProbe_probability_le_profile
    {B₀ C₄ C₃ c C Q g : ℝ} (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (n : ℕ) (P : Probe) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh≤P.innerRadius)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*Q) (hKH : 1≤C₃*Q/c)
    (hp : ∀ t, 0<t → t≤P.outerRadius → 0<p t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤Q*(p a/p b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → p b≤C*(b/a)^g*p a)
    (hfourlower : ∀ a b, B₀*P.mesh≤a → 0<a → a≤b → b≤P.outerRadius → c*(a/b)^g≤α a b) :
    probability (fairSites D) (fun ω => StraightProbeArms n P (completeColors D ω)) ≤
      fullProbeConstant C₄ C₃ c C Q g*(p P.innerRadius/p P.outerRadius) := by
  have hC0 : 0≤C := by linarith
  have hKB0 : 0≤C₄*Q := by linarith
  have hKH0 : 0≤C₃*Q/c := by linarith
  have hrR : P.innerRadius≤P.outerRadius := by linarith [P.radii,P.inner_pos]
  have hR : 0<P.outerRadius := P.inner_pos.trans_le hrR
  have hpRatio : 0≤p P.innerRadius/p P.outerRadius :=
    div_nonneg (hp _ P.inner_pos hrR).le (hp _ hR le_rfl).le
  have hMix : 0≤(C₄*Q)*(C₃*Q/c)*C^3*(8192:ℝ)^g := by positivity
  have hInt : 0≤(C₄*Q)*C^2*(16:ℝ)^g := by positivity
  by_cases h : HasSideContact n P
  · simp only [StraightProbeArms,dite_eq_left h]
    apply (mixed_probability_le_profile α p hfour hthree P (boxHalfPlane n h.choose)
      (boxSideProjection n h.choose (HexCells.center P.center))
      (boxSideProjection_boundary n h.choose (HexCells.center P.center)) D hD hmesh
      hg0 hg2 hc hC₃ hC₄ hC hKB hKH hp hquasi hlower hfourlower).trans
    unfold fullProbeConstant
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hInt) hpRatio
  · simp only [StraightProbeArms,dite_eq_right h]
    apply (interior_probability_le_profile α p hfour P D hD hmesh hg0 hC hC₄ hKB hp hquasi hlower).trans
    unfold fullProbeConstant
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hMix) hpRatio

#print axioms life_straightProbeArms
#print axioms straightProbeArms_locality
#print axioms straightProbe_probability_le_profile

end ExceptionalTimes.PairSquareSewing
