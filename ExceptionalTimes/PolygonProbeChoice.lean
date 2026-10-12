import ExceptionalTimes.PolygonMixedProbe
import ExceptionalTimes.FullLifeProbe

/-! The selected event is explicitly either the inset bulk arm event or
the two disjoint mixed pieces. Its selection is purely geometric, and its
probability follows from the published individual static arm bounds. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct

inductive PolygonArmChoice (P : Probe) where
  | bulk
  | boundary (H : LatticeHalfPlane) (q : ℝ × ℝ) (hq : q ∈ H.boundary)

def PolygonArmChoice.event {P : Probe} (choice : PolygonArmChoice P)
    (ω : Configuration) : Prop :=
  match choice with
  | .bulk => InteriorProbeArms P ω
  | .boundary H q hq => MixedBoundaryArms P H q hq ω

theorem PolygonArmChoice.locality {P : Probe} (choice : PolygonArmChoice P)
    {ω η : Configuration} (heq : EqOn ω η P.region) :
    choice.event ω ↔ choice.event η := by
  cases choice with
  | bulk => exact forall_congr' (fun h => fourArms_eqOn (heq.mono (P.inset_region h)))
  | boundary H q hq => exact MixedBoundaryArms.locality P H q hq heq

theorem exists_polygonArmChoice {Q : PolygonQuad} {E : Type*}
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (A : AxialPolygonPresentation Q E) (P : Probe) {δ : ℝ}
    (he : 16*P.mesh<P.innerRadius) (hscale : 6*P.outerRadius<P.mesh*δ)
    (hparallel : ∀ i j, (A.edge i).horizontal=(A.edge j).horizontal →
      (A.edge i).level≠(A.edge j).level → δ≤|(A.edge i).level-(A.edge j).level|)
    (hroots : ∀ i,
      8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (A.edge i).first) ∧
      8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (A.edge i).last))
    (hinteger : ∀ i, ∃ level : ℤ, (A.edge i).level=(level:ℝ)) :
    ∃ choice : PolygonArmChoice P, ∀ ω a b : Configuration,
      (∀ v, v ∉ P.pocket → a v=b v) → EqOn a ω P.region → EqOn b ω P.region →
      ¬ (Q.Crossing a ↔ Q.Crossing b) → choice.event ω := by
  by_cases hc : ∃ i, (A.edge i).contact P.mesh (HexCells.center P.center) P.outerRadius
  · obtain ⟨i,hi⟩ := hc
    obtain ⟨level,hlevel⟩ := hinteger i
    obtain ⟨H,hq,hnecessary⟩ := polygon_mixedBoundaryArms hbulk hhalf A P he hscale
      hparallel hroots i hi level hlevel
    exact ⟨.boundary H _ hq,hnecessary⟩
  · refine ⟨.bulk,?_⟩
    intro ω a b hab ha hb hchange hactive
    apply polygon_fourArms_of_no_contact hbulk Q (P.inset hactive) A.edge A.frontier_iff he _
      ω a b hab (ha.mono (P.inset_region hactive)) (hb.mono (P.inset_region hactive)) hchange
    intro i hi
    apply hc
    obtain ⟨t,ht,hd⟩ := hi
    refine ⟨i,t,ht,?_⟩
    change dist (axialPhysical P.mesh (HexCells.center P.center))
      (axialPhysical P.mesh ((A.edge i).point t))≤2*(P.outerRadius/4) at hd
    change dist (axialPhysical P.mesh (HexCells.center P.center))
      (axialPhysical P.mesh ((A.edge i).point t))≤2*P.outerRadius
    linarith [P.radii,P.inner_pos]

theorem PolygonArmChoice.probability_le_profile
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (P : Probe) (choice : PolygonArmChoice P) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh≤P.innerRadius)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hp : ∀ t, 0<t → t≤P.outerRadius → 0<p t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤K*(p a/p b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → p b≤C*(b/a)^g*p a)
    (hfourlower : ∀ a b, B₀*P.mesh≤a → 0<a → a≤b → b≤P.outerRadius → c*(a/b)^g≤α a b) :
    probability (fairSites D) (fun ω => choice.event (completeColors D ω)) ≤
      fullProbeConstant C₄ C₃ c C K g*(p P.innerRadius/p P.outerRadius) := by
  have hC0 : 0≤C := by linarith
  have hKB0 : 0≤C₄*K := by linarith
  have hKH0 : 0≤C₃*K/c := by linarith
  have hrR : P.innerRadius≤P.outerRadius := by linarith [P.radii,P.inner_pos]
  have hR : 0<P.outerRadius := P.inner_pos.trans_le hrR
  have hpRatio : 0≤p P.innerRadius/p P.outerRadius :=
    div_nonneg (hp _ P.inner_pos hrR).le (hp _ hR le_rfl).le
  have hMix : 0≤(C₄*K)*(C₃*K/c)*C^3*(8192:ℝ)^g := by positivity
  have hInt : 0≤(C₄*K)*C^2*(16:ℝ)^g := by positivity
  cases choice with
  | bulk =>
    apply (interior_probability_le_profile α p hfour P D hD hmesh hg0 hC hC₄ hKB hp hquasi hlower).trans
    unfold fullProbeConstant
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hMix) hpRatio
  | boundary H q hq =>
    apply (mixed_probability_le_profile α p hfour hthree P H q hq D hD hmesh
      hg0 hg2 hc hC₃ hC₄ hC hKB hKH hp hquasi hlower hfourlower).trans
    unfold fullProbeConstant
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hInt) hpRatio

#print axioms exists_polygonArmChoice
#print axioms PolygonArmChoice.probability_le_profile

end ExceptionalTimes.PairSquareSewing
