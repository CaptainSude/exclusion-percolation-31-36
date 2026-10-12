import ExceptionalTimes.MixedBoundaryProbes
import ExceptionalTimes.HalfArmComparison
import ExceptionalTimes.LocalEventIndependence

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct

theorem FourArms.mono_eqOn {P : Probe} {ω η : Configuration}
    (h : FourArms P ω) (heq : EqOn ω η P.region) : FourArms P η := by
  obtain ⟨s,t,p,hp,hs,ht,hcol,hdis,contacts⟩ := h
  refine ⟨s,t,p,hp,hs,ht,?_,hdis,contacts⟩
  intro i z hz
  have hh := hcol i z hz
  exact ⟨hh.1,(heq hh.1).symm.trans hh.2⟩

theorem fourArms_eqOn {P : Probe} {ω η : Configuration}
    (heq : EqOn ω η P.region) : FourArms P ω ↔ FourArms P η :=
  ⟨fun h => h.mono_eqOn heq,fun h => h.mono_eqOn heq.symm⟩

theorem completeColors_eqOn (D : Finset Site) (S : Set Site) {ω η : D → Bool}
    (h : EqOn ω η {v : D | v.val ∈ S}) :
    EqOn (completeColors D ω) (completeColors D η) S := by
  intro v hv
  by_cases hd : v ∈ D
  · simpa only [completeColors,dite_eq_left hd] using h (x := ⟨v,hd⟩) hv
  · simp only [completeColors,dite_eq_right hd]

/-- Literal finite fair-site factorization; the required disjointness is
geometric disjointness of the actual path-support regions. -/
theorem bulk_half_probability_product (B : Probe) (H : HalfProbe) (D : Finset Site)
    (hdis : Disjoint B.region H.region) :
    probability (fairSites D) (fun ω => FourArms B (completeColors D ω) ∧
      HalfThreeArms H (completeColors D ω)) =
      probability (fairSites D) (fun ω => FourArms B (completeColors D ω)) *
      probability (fairSites D) (fun ω => HalfThreeArms H (completeColors D ω)) := by
  apply fairSites_two_local {v : D | v.val ∈ B.region} {v : D | v.val ∈ H.region}
  · exact Set.disjoint_left.mpr (fun _ hb hh => Set.disjoint_left.mp hdis hb hh)
  · exact fun _ _ heq => fourArms_eqOn (completeColors_eqOn D B.region heq)
  · exact fun _ _ heq => halfThreeArms_eqOn (completeColors_eqOn D H.region heq)

/-- Standard circular-buffer version of the published single four-arm
estimate. The comparison constant records the fixed change from square
annuli, and the source's microscopic cutoff remains explicit. -/
def PublishedFourArmBound (B₀ C : ℝ) (α : ℝ → ℝ → ℝ) : Prop :=
  ∀ (P : Probe) (D : Finset Site), B₀*P.mesh ≤ P.innerRadius →
    P.region ⊆ (D : Set Site) →
    probability (fairSites D) (fun ω => FourArms P (completeColors D ω)) ≤
      C*α P.innerRadius P.outerRadius

/-- The one-probe mixed bound is derived from two published individual
static estimates and proved independence of the actual disjoint supports. -/
theorem mixed_active_probability_bound
    {B₀ C₄ C₃ c g : ℝ} (α : ℝ → ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ) (hq : q ∈ H.boundary)
    (hb : BulkPartActive P q) (hh : HalfPartActive P q) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh ≤ P.innerRadius)
    (hg : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hα : 0≤α P.innerRadius (min P.outerRadius (P.distanceTo q/8)))
    (hlower : c*((8*max P.innerRadius (P.distanceTo q))/(P.outerRadius/8))^g ≤
      α (8*max P.innerRadius (P.distanceTo q)) (P.outerRadius/8)) :
    probability (fairSites D) (fun ω => MixedBoundaryArms P H q hq (completeColors D ω)) ≤
      (C₄*C₃/c)*α P.innerRadius (min P.outerRadius (P.distanceTo q/8)) *
        α (8*max P.innerRadius (P.distanceTo q)) (P.outerRadius/8) := by
  have heq : probability (fairSites D) (fun ω => MixedBoundaryArms P H q hq (completeColors D ω)) =
      probability (fairSites D) (fun ω => FourArms (P.bulkPart q hb) (completeColors D ω) ∧
        HalfThreeArms (P.halfPart H q hq hh) (completeColors D ω)) := by
    apply probability_congr
    intro ω
    exact ⟨fun h => ⟨h.1 hb,h.2 hh⟩,fun h => ⟨fun _ => h.1,fun _ => h.2⟩⟩
  rw [heq,bulk_half_probability_product _ _ D (P.bulk_half_disjoint H q hq hb hh)]
  have hfour' := hfour (P.bulkPart q hb) D hmesh ((P.bulkPart_region q hb).trans hD)
  have hhalfmesh : B₀*(P.halfPart H q hq hh).mesh ≤ (P.halfPart H q hq hh).innerRadius := by
    change B₀*P.mesh ≤ 8*max P.innerRadius (P.distanceTo q)
    have hm := le_max_left P.innerRadius (P.distanceTo q)
    linarith [P.inner_pos]
  have hthree' := halfThree_probability_le_four hthree (P.halfPart H q hq hh) D hhalfmesh
    ((P.halfPart_region H q hq hh).trans hD) hg hc hC₃ α hlower
  have hprod := mul_le_mul hfour' hthree' (probability_nonneg _ _) (mul_nonneg hC₄ hα)
  convert hprod using 1
  dsimp [Probe.bulkPart,Probe.halfPart]
  ring

#print axioms bulk_half_probability_product
#print axioms mixed_active_probability_bound

end ExceptionalTimes.PairSquareSewing

