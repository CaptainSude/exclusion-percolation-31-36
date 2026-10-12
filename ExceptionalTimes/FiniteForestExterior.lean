import ExceptionalTimes.FixedMeshSelectedForest
import ExceptionalTimes.SourceSampling
import ExceptionalTimes.UnitReferenceCover

/-! Every finite forest has an actual finite independent exterior containing
all of its probe regions and crossing tests. The exterior can be chosen
separately for each selected set; no geometric coverage premise is needed. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.FiniteForestExterior
noncomputable section
open PairSquareSewing FixedMeshSelectedForest DimerSelectedDictionary
open DimerExpansion CenteredBlocks BlockExpansion CanonicalSpatialProduct

variable {I J : Type*} [Fintype I] [Fintype J]

def activeLives (G : DimerGeometry I J) (cutoff stop : ℝ) :=
  {a : DimerLife G cutoff stop // LifeProbeActive G cutoff stop a}

instance (G : DimerGeometry I J) (cutoff stop : ℝ) : Fintype (activeLives G cutoff stop) :=
  inferInstanceAs (Fintype {a : DimerLife G cutoff stop // LifeProbeActive G cutoff stop a})

def probeSites (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff) : Finset Site :=
  Finset.univ.biUnion (fun a : activeLives G cutoff stop =>
    let P := dimerLifeProbe G cutoff stop hcut a.val a.property
    sourceDiskSites P.mesh P.mesh_pos P.center (2*P.outerRadius))

theorem probeSites_covers (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (a : DimerLife G cutoff stop) (ha : LifeProbeActive G cutoff stop a) :
    (dimerLifeProbe G cutoff stop hcut a ha).region ⊆ (probeSites G cutoff stop hcut : Set Site) := by
  intro v hv
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨a,ha⟩,Finset.mem_univ _,probe_region_subset_disk _ hv⟩

omit [Fintype I] [Fintype J] in
theorem unit_cover_span (ε : ℝ) (hε : 0<ε) (D : Finset Site)
    (i : UnitReferenceCover.anchors false D) (e f : Fin 2) :
    dist (position ε (UnitReferenceCover.slot false D (i,e)))
      (position ε (UnitReferenceCover.slot false D (i,f)))≤ε := by
  let G := displacedDimerGeometry ε hε (1,0) (UnitReferenceCover.slot false D)
    (UnitReferenceCover.slot_positive false D) (fun _ : Empty => (0:ℂ))
  have h := G.pairwise_bound i e f
  have hunit : triangularEmbedding ((1,0) : Site)=(1:ℂ) := by
    apply Complex.ext <;> norm_num [triangularEmbedding]
  simpa only [G,displacedDimerGeometry,hunit,norm_one,mul_one,max_self] using h

#print axioms probeSites_covers
#print axioms unit_cover_span
end
end ExceptionalTimes.FiniteForestExterior
