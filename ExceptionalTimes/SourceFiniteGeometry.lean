import ExceptionalTimes.PolygonScaling
import ExceptionalTimes.PolygonCrossingLocality
import ExceptionalTimes.FairSiteRestriction
import ExceptionalTimes.SourceTrialSymmetry

/-! Concrete finite geometry and fair-field restrictions for source06.
The polygons are fixed before the mesh; insertion tuples lie in one compact
range with a uniform positive distance from one another and every polygon
boundary. Literal physical disks and polygon supports produce finite site
sets. Enlarging those sets preserves the actual two-source iid law.
No seam probability, dynamical transfer, or arbitrary conditional-field
estimate is assumed in this module.
-/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

noncomputable section

open EnvironmentVariance ProbeProduct

/-- The source's fixed finite polygon tests and fixed compact separated
location range, expressed in the physical plane. The integration box is
also fixed before the mesh. -/
structure SourceSeparatedGeometry (q k : ℕ) where
  quads : Fin q → PolygonQuad
  locations : Set (Fin (k+1) → ℂ)
  compact_locations : IsCompact locations
  margin : ℝ
  margin_pos : 0 < margin
  boxRadius : ℝ
  separated : ∀ x ∈ locations, ∀ i j, i≠j → margin ≤ dist (x i) (x j)
  boundary_separated : ∀ x ∈ locations, ∀ i j, ∀ y ∈ frontier (quads j).carrier,
    margin ≤ dist (x i) (HexTiling.planeMap y)
  box_separated : ∀ x ∈ locations, ∀ i, ‖x i‖+margin ≤ boxRadius

noncomputable def SourceSeparatedGeometry.latticeQuads {q k : ℕ}
    (G : SourceSeparatedGeometry q k) (e : ℝ) (he : 0<e) : Fin q → PolygonQuad :=
  fun i => (G.quads i).scale e⁻¹ (inv_ne_zero he.ne')

def SourceSeparatedGeometry.Admissible {q k : ℕ}
    (G : SourceSeparatedGeometry q k) (e : ℝ) (x : Fin (k+1) → Site) : Prop :=
  (fun i => position e (x i)) ∈ G.locations

/-- The actual mesh-e embedding, independently of any probe radii. -/
noncomputable def sourcePhysicalMap (e : ℝ) (he : 0<e) : (ℝ×ℝ) ≃ₜ ℂ :=
  axialPlaneHomeomorph.trans (Homeomorph.mulLeft₀ (e : ℂ) (by exact_mod_cast he.ne'))

theorem sourcePhysicalMap_center (e : ℝ) (he : 0<e) (v : Site) :
    sourcePhysicalMap e he (HexCells.center v)=position e v := rfl

/-- Every hexagonal cell meeting the literal closed physical disk.
Compactness proves this is a finite set; no artificial cutoff is chosen. -/
noncomputable def sourceDiskSites (e : ℝ) (he : 0<e) (x : Site) (R : ℝ) : Finset Site :=
  (finite_cellSupport ((isCompact_closedBall (position e x) R).image
    (sourcePhysicalMap e he).symm.continuous)).toFinset

theorem mem_sourceDiskSites (e : ℝ) (he : 0<e) (x v : Site) (R : ℝ) :
    v ∈ sourceDiskSites e he x R ↔
      (HexCells.cell v ∩ ((sourcePhysicalMap e he).symm ''
        Metric.closedBall (position e x) R)).Nonempty := by
  simp [sourceDiskSites,cellSupport]

theorem center_mem_sourceDiskSites (e : ℝ) (he : 0<e) (x v : Site) (R : ℝ)
    (hv : dist (position e v) (position e x)≤R) :
    v ∈ sourceDiskSites e he x R := by
  apply (mem_sourceDiskSites e he x v R).mpr
  refine ⟨HexCells.center v,HexCells.center_mem_cell v,?_⟩
  refine ⟨sourcePhysicalMap e he (HexCells.center v),?_,by simp⟩
  simpa only [sourcePhysicalMap_center,Metric.mem_closedBall] using hv

/-- A literal finite sample containing every tested polygon and every
cell meeting a chosen macroscopic disk about an insertion. -/
noncomputable def SourceSeparatedGeometry.sampleSites {q k : ℕ}
    (G : SourceSeparatedGeometry q k) (e : ℝ) (he : 0<e)
    (x : Fin (k+1) → Site) (R : ℝ) : Finset Site :=
  polygonFamilySupport (G.latticeQuads e he) ∪
    Finset.univ.biUnion (fun i => sourceDiskSites e he (x i) R)

theorem SourceSeparatedGeometry.polygon_support_subset {q k : ℕ}
    (G : SourceSeparatedGeometry q k) (e : ℝ) (he : 0<e)
    (x : Fin (k+1) → Site) (R : ℝ) :
    polygonFamilySupport (G.latticeQuads e he) ⊆ G.sampleSites e he x R :=
  Finset.subset_union_left

theorem SourceSeparatedGeometry.disk_sites_subset {q k : ℕ}
    (G : SourceSeparatedGeometry q k) (e : ℝ) (he : 0<e)
    (x : Fin (k+1) → Site) (R : ℝ) (i : Fin (k+1)) :
    sourceDiskSites e he (x i) R ⊆ G.sampleSites e he x R := by
  intro v hv
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hv⟩)

/-- Exact two-source restriction, retaining independence of the two raw
fields. It is not a statement conditional on arbitrary exterior events. -/
theorem source_expect_restrict (S D : Finset Site) (hSD : S⊆D)
    (F : Configuration → Configuration → ℝ)
    (hlocal : ∀ a b a' b',
      (∀ v∈S,a v=a' v) → (∀ v∈S,b v=b' v) → F a b=F a' b') :
    (sourceLaw D).expect (fun ω => F (complete ω.1) (complete ω.2)) =
      (sourceLaw S).expect (fun ω => F (complete ω.1) (complete ω.2)) := by
  simp only [sourceLaw,FiniteLaw.expect_prod]
  calc
    _ = (fairSites D).expect (fun a => (fairSites S).expect
        (fun b => F (complete a) (complete b))) := by
      apply FiniteLaw.expect_congr
      intro a
      exact FiniteSiteLaw.fairSites_restrict S D hSD (F (complete a))
        (fun b b' hb => hlocal _ _ _ _ (fun _ _ => rfl) hb)
    _ = _ := FiniteSiteLaw.fairSites_restrict S D hSD
      (fun a => (fairSites S).expect (fun b => F a (complete b)))
      (fun a a' ha => FiniteLaw.expect_congr _
        (fun b => hlocal _ _ _ _ ha (fun _ _ => rfl)))

theorem source_probability_restrict (S D : Finset Site) (hSD : S⊆D)
    (E : Configuration → Configuration → Prop)
    (hlocal : ∀ a b a' b',
      (∀ v∈S,a v=a' v) → (∀ v∈S,b v=b' v) → (E a b ↔ E a' b')) :
    probability (sourceLaw D) (fun ω => E (complete ω.1) (complete ω.2)) =
      probability (sourceLaw S) (fun ω => E (complete ω.1) (complete ω.2)) :=
  source_expect_restrict S D hSD (fun a b => indicator (E a b))
    (fun a b a' b' ha hb => congrArg indicator (propext (hlocal a b a' b' ha hb)))

#print axioms center_mem_sourceDiskSites
#print axioms SourceSeparatedGeometry.disk_sites_subset
#print axioms source_expect_restrict
#print axioms source_probability_restrict

end
end ExceptionalTimes.PairSquareSewing
