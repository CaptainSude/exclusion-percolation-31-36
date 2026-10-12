import ExceptionalTimes.SourceCompactGeometry
import ExceptionalTimes.DyadicFiniteFamily

/-! The uniform sewing comparison for exactly the dyadic physical tests
used in the expansion. The scaled polygons and the counted bad tuples
are identified, not supplied as separate matching hypotheses. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open IndependentAnnulusInput LocalDimerCalibration

def dyadicSourcePolygons {q : ℕ} (T : DyadicQuadFamily (Fin q))
    (hplane : PublishedInvarianceOfDomain) : Fin q→PolygonQuad :=
  fun i => (T.grid i).polygon hplane

theorem dyadic_polygon_scale {q : ℕ} (T : DyadicQuadFamily (Fin q))
    (hplane : PublishedInvarianceOfDomain) (n : ℕ) (i : Fin q) :
    ((dyadicSourcePolygons T hplane) i).scale (mesh n)⁻¹ (inv_ne_zero (mesh_pos n).ne')=
      (T.grid i).meshPolygon hplane n := by
  simp only [dyadicSourcePolygons,mesh,inv_inv,DyadicGridQuad.meshPolygon]

theorem compact_dyadic_latticeQuads {q k : ℕ} (T : DyadicQuadFamily (Fin q))
    (hplane : PublishedInvarianceOfDomain) (center : ℂ) (r δ : ℝ) (hδ : 0<δ) (n : ℕ) :
    (compactGeometry (k:=k) (dyadicSourcePolygons T hplane) center r δ hδ).latticeQuads (mesh n) (mesh_pos n)=
      fun i => (T.grid i).meshPolygon hplane n := by
  funext i
  exact dyadic_polygon_scale T hplane n i

theorem compact_dyadic_test {q k : ℕ} (T : DyadicQuadFamily (Fin q))
    (hplane : PublishedInvarianceOfDomain) (center : ℂ) (r δ : ℝ) (hδ : 0<δ)
    (n : ℕ) (hn : T.maxLevel≤n) (i : Fin q) (ω : Configuration) :
    ((compactGeometry (k:=k) (dyadicSourcePolygons T hplane) center r δ hδ).latticeQuads
      (mesh n) (mesh_pos n) i).test ω=T.test n i ω := by
  rw [compact_dyadic_latticeQuads (k:=k) T hplane center r δ hδ n]
  exact (T.test_eq hplane n hn i ω).symm

theorem uniform_good_tuple_normalized_limit {q k : ℕ} (T : DyadicQuadFamily (Fin q))
    (hplane : PublishedInvarianceOfDomain) (center : ℂ) (r δ : ℝ) (hδ : 0<δ) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) (hattach : UnitStaticAttachment.PublishedUnitAttachment B) :
    ∀η : ℝ,0<η→∃N : ℕ,∀n : ℕ,N≤n→∀s : Finset Site,
      (∀v∈s,‖LatticeRadial.scaledEmbedding (mesh n) v-center‖≤r)→
      ∀x : Fin (k+1)→s,
      x∉LatticeBoundaryMass.polygonBadTuples s (k+1) (dyadicSourcePolygons T hplane) (mesh n) δ→
      ∀endpoint : Fin (k+1)×Fin 2 ↪ Site,
      (∀j,endpoint (j,0)=(x j).val)→(∀j,endpoint (j,1)=(x j).val+(1,0))→
      ∀Λ : Finset Site,(∀i,((T.grid i).meshPolygon hplane n).support⊆Λ)→
      ∀r₁ r₂ : Rule,∀outer : (Fin q×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→
      |fullCoefficient Λ endpoint (fun _ => r₁)
        (fun ξ => outer (fun qt => T.test n qt.1 (ξ qt.2)))/(localS r₁ n)^(k+1)-
       fullCoefficient Λ endpoint (fun _ => r₂)
        (fun ξ => outer (fun qt => T.test n qt.1 (ξ qt.2)))/(localS r₂ n)^(k+1)|<η := by
  intro η hη
  let G := compactGeometry (k:=k) (dyadicSourcePolygons T hplane) center r δ hδ
  obtain ⟨N,hlim⟩ := uniform_dyadic_full_normalized_limit G B hseams hstatic hbulk hlower harmlower hattach η hη
  refine ⟨max N T.maxLevel,?_⟩
  intro n hn s hs x hx endpoint h0 h1 Λ hΛ r₁ r₂ outer hout
  have hnN : N≤n := (le_max_left _ _).trans hn
  have hnT : T.maxLevel≤n := (le_max_right _ _).trans hn
  have ha := compactGeometry_admissible_of_not_bad (dyadicSourcePolygons T hplane)
    center r δ hδ s (mesh n) hs x hx
  have hcover : polygonFamilySupport (G.latticeQuads (mesh n) (mesh_pos n))⊆Λ := by
    intro v hv
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
    rw [compact_dyadic_latticeQuads (k:=k) T hplane center r δ hδ n] at hi
    exact hΛ i hi
  have h := hlim n hnN (fun j => (x j).val) ha endpoint h0 h1 Λ hcover r₁ r₂ outer hout
  have hfun : (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads (mesh n) (mesh_pos n)) ξ))=
      fun ξ => outer (fun qt => T.test n qt.1 (ξ qt.2)) := by
    funext ξ
    apply congrArg outer
    funext qt
    exact compact_dyadic_test (k:=k) T hplane center r δ hδ n hnT qt.1 (ξ qt.2)
  rwa [hfun] at h

#print axioms compact_dyadic_test
#print axioms uniform_good_tuple_normalized_limit
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization

