import ExceptionalTimes.SourceFullNormalizedLimit

/-! The actual dyadic-mesh coefficient comparison in the normalization
used by the local clocks. Auxiliary finite sample sites are summed out.
This is a pointwise uniform compact-separated result; summing anchors and
removing collision/boundary strips are separate analytic steps. -/
open Filter
open scoped Classical BigOperators Topology
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open IndependentAnnulusInput LocalDimerCalibration

theorem uniform_dyadic_full_normalized_limit {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) (hattach : UnitStaticAttachment.PublishedUnitAttachment B) :
    ∀δ : ℝ,0<δ→∃N : ℕ,∀n : ℕ,N≤n→
      ∀x : Fin (k+1)→Site,G.Admissible (mesh n) x→
      ∀endpoint : Fin (k+1)×Fin 2 ↪ Site,
      (∀j,endpoint (j,0)=x j)→(∀j,endpoint (j,1)=x j+(1,0))→
      ∀Λ : Finset Site,polygonFamilySupport (G.latticeQuads (mesh n) (mesh_pos n))⊆Λ→
      ∀r₁ r₂ : Rule,∀outer : (Fin q×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→
      |fullCoefficient Λ endpoint (fun _ => r₁)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads (mesh n) (mesh_pos n)) ξ)) /
          (localS r₁ n)^(k+1)-
       fullCoefficient Λ endpoint (fun _ => r₂)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads (mesh n) (mesh_pos n)) ξ)) /
          (localS r₂ n)^(k+1)|<δ := by
  intro δ hδ
  obtain ⟨e0,he0,hbound⟩ := uniform_full_normalized_limit G B hseams hstatic hbulk hlower harmlower hattach δ hδ
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (UnitClockControl.mesh_tendsto_zero.eventually (gt_mem_nhds he0))
  refine ⟨N,?_⟩
  intro n hn x hx endpoint h0 h1 Λ hΛ r₁ r₂ outer hout
  have htest (j : Fin q) : (G.latticeQuads (mesh n) (mesh_pos n) j).support⊆
      polygonFamilySupport (G.latticeQuads (mesh n) (mesh_pos n)) :=
    fun v hv => Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hv⟩
  have hres (r : Rule) := fullCoefficient_restrict_polygons (G.latticeQuads (mesh n) (mesh_pos n))
    (polygonFamilySupport (G.latticeQuads (mesh n) (mesh_pos n))) Λ hΛ htest outer endpoint (fun _ => r)
  rw [hres r₁,hres r₂]
  simpa only [centralS_dyadic] using hbound (mesh n) (mesh_pos n) (hN n hn) x hx endpoint h0 h1 r₁ r₂ outer hout

#print axioms uniform_dyadic_full_normalized_limit
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization
