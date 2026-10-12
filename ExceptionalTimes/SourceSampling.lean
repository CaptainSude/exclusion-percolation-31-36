import ExceptionalTimes.SourceReferenceGeometry
import ExceptionalTimes.SourcePolygonCalibration

/-! Literal square forcing sites and circular arm normalization for source06.
The square is a physical, closed, axis-aligned square. Its finite set contains
exactly the cells meeting that square. The arm cost is an actual ordinary
fair-color probability, not an arbitrary normalization parameter. -/

open Set
open scoped Classical
namespace ExceptionalTimes.PairSquareSewing
noncomputable section
open EnvironmentVariance ProbeProduct

noncomputable def sourcePhysicalSquare (c : ℂ) (h : ℝ) : Set ℂ :=
  (fun p : ℝ×ℝ => c + (⟨p.1,p.2⟩ : ℂ)) '' ((Icc (-h) h).prod (Icc (-h) h))

theorem isCompact_sourcePhysicalSquare (c : ℂ) (h : ℝ) :
    IsCompact (sourcePhysicalSquare c h) :=
    (isCompact_Icc.prod isCompact_Icc).image (by
    have hc : Continuous (fun p : ℝ×ℝ => c + (p.1 : ℂ) + (p.2 : ℂ)*Complex.I) := by fun_prop
    convert hc using 1
    funext p
    apply Complex.ext <;> simp)

theorem sourcePhysicalSquare_radius {c z : ℂ} {h : ℝ}
    (hz : z ∈ sourcePhysicalSquare c h) : dist z c ≤ 2*h := by
  obtain ⟨p,hp,rfl⟩ := hz
  have hp' := Set.mem_prod.mp hp
  have hx : |p.1|≤h := abs_le.mpr hp'.1
  have hy : |p.2|≤h := abs_le.mpr hp'.2
  rw [dist_eq_norm]
  simp only [add_sub_cancel_left]
  exact (Complex.norm_le_abs_re_add_abs_im (⟨p.1,p.2⟩ : ℂ)).trans (by dsimp; linarith)

noncomputable def sourceSquareSites (e : ℝ) (he : 0<e) (x : Site) (h : ℝ) : Finset Site :=
  (finite_cellSupport ((isCompact_sourcePhysicalSquare (position e x) h).image
    (sourcePhysicalMap e he).symm.continuous)).toFinset

theorem mem_sourceSquareSites (e : ℝ) (he : 0<e) (x v : Site) (h : ℝ) :
    v ∈ sourceSquareSites e he x h ↔
      (HexCells.cell v ∩ ((sourcePhysicalMap e he).symm ''
        sourcePhysicalSquare (position e x) h)).Nonempty := by
  simp [sourceSquareSites,cellSupport]

theorem sourceSquareSites_radius (e : ℝ) (he : 0<e) (x v : Site) (h : ℝ)
    (hv : v ∈ sourceSquareSites e he x h) :
    dist (position e v) (position e x) ≤ 2*e+2*h := by
  obtain ⟨p,hp,z,hz,hzp⟩ := (mem_sourceSquareSites e he x v h).mp hv
  have hpz : sourcePhysicalMap e he p=z := by rw [← hzp]; simp
  have hzcell : z ∈ HexTiling.physicalCell e v := ⟨p,hp,hpz⟩
  have hcell := HexTiling.physicalCell_radius hzcell
  have hsquare := sourcePhysicalSquare_radius hz
  rw [abs_of_pos he] at hcell
  change dist z (position e v) ≤ 2*e at hcell
  have ht := dist_triangle (position e v) z (position e x)
  rw [dist_comm (position e v) z] at ht
  linarith

theorem sourceSquareSites_subset_disk (e : ℝ) (he : 0<e) (x : Site) (h R : ℝ)
    (hR : 2*h≤R) : sourceSquareSites e he x h ⊆ sourceDiskSites e he x R := by
  intro v hv
  obtain ⟨p,hp,z,hz,hzp⟩ := (mem_sourceSquareSites e he x v h).mp hv
  apply (mem_sourceDiskSites e he x v R).mpr
  exact ⟨p,hp,z,Metric.mem_closedBall.mpr ((sourcePhysicalSquare_radius hz).trans hR),hzp⟩

theorem sourceSquareSites_subset_pocket (P : Probe) (h : ℝ)
    (hbuffer : 2*P.mesh+2*h<P.innerRadius/2) :
    (sourceSquareSites P.mesh P.mesh_pos P.center h : Set Site) ⊆ P.pocket := by
  intro v hv
  exact (sourceSquareSites_radius P.mesh P.mesh_pos P.center v h hv).trans_lt hbuffer

theorem probe_region_subset_disk (P : Probe) :
    P.region ⊆ (sourceDiskSites P.mesh P.mesh_pos P.center (2*P.outerRadius) : Set Site) := by
  intro v hv
  exact center_mem_sourceDiskSites P.mesh P.mesh_pos P.center v (2*P.outerRadius) hv.2

noncomputable def sourceCircularProbe (e r : ℝ) (he : 0<e) (hr : 0<r)
    (hsmall : 4*r<1) : Probe := ⟨e,(0,0),r,1,he,hr,hsmall⟩

/-- The circular-cut version of A_e(r,1). Source02 bounded-shape and
cut-margin quasi-multiplicativity is needed when comparing this number
with the source's square-annulus normalization. No equality is claimed. -/
noncomputable def sourceArmCost (e r : ℝ) (he : 0<e) (hr : 0<r) (hsmall : 4*r<1) : ℝ :=
  probability (fairSites (sourceDiskSites e he (0,0) 2))
    (fun ω => FourArms (sourceCircularProbe e r he hr hsmall) (complete ω))

theorem sourceArmCost_nonneg (e r : ℝ) (he : 0<e) (hr : 0<r) (hsmall : 4*r<1) :
    0≤sourceArmCost e r he hr hsmall := probability_nonneg _ _

theorem sourceArmCost_le_one (e r : ℝ) (he : 0<e) (hr : 0<r) (hsmall : 4*r<1) :
    sourceArmCost e r he hr hsmall≤1 := probability_le_one _ _

/-- Enlarging the ordinary iid sample leaves the literal arm cost exact.
This is the finite/full-plane cylinder dictionary needed by the source. -/
theorem sourceArmCost_enlargement (e r : ℝ) (he : 0<e) (hr : 0<r) (hsmall : 4*r<1)
    (D : Finset Site) (hD : sourceDiskSites e he (0,0) 2 ⊆ D) :
    probability (fairSites D)
      (fun ω => FourArms (sourceCircularProbe e r he hr hsmall) (complete ω)) =
      sourceArmCost e r he hr hsmall := by
  apply FiniteSiteLaw.fairSites_restrict _ D hD
    (fun ω => indicator (FourArms (sourceCircularProbe e r he hr hsmall) ω))
  intro ω η h
  apply congrArg indicator
  apply propext
  apply fourArms_congr
  intro v hv
  apply h v
  simpa only [sourceCircularProbe, mul_one, Finset.mem_coe] using
    probe_region_subset_disk (sourceCircularProbe e r he hr hsmall) hv

#print axioms sourceSquareSites_radius
#print axioms sourceSquareSites_subset_pocket
#print axioms sourceArmCost_enlargement
end
end ExceptionalTimes.PairSquareSewing


