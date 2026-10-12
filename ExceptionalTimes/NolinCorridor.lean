import ExceptionalTimes.AnnularCircuitProbability
import ExceptionalTimes.HalfPlaneArms
import ExceptionalTimes.CanonicalRadialLaw

/-! Literal endpoint-free rectangle crossings in Nolin (2008), sections
2.1 and 2.3. The endpoint convention is retained. A one-layer buffer
then gives our original-color radial event by an actual lattice walk.
The RSW estimate is an explicit published input, never a new axiom. -/

namespace ExceptionalTimes.NolinCorridor

open HoleFilling WiredBoundary AnnularCollars EnvironmentVariance ProbeProduct
open PairSquareSewing
open scoped Classical

def rectangle (M n : ℕ) : Finset Site :=
  (Finset.Icc (0 : ℤ) M) ×ˢ (Finset.Icc (0 : ℤ) n)

/-- The two endpoints are uncolored; all other path vertices lie in
the strict interior and are black, as in the source convention. -/
def HorizontalCrossing (ω : Configuration) (M n : ℕ) : Prop :=
  ∃ u v : Site, u.1 = 0 ∧ 0 ≤ u.2 ∧ u.2 ≤ n ∧
    v.1 = M ∧ 0 ≤ v.2 ∧ v.2 ≤ n ∧
    ∃ p : triangularGraph.Walk u v, p.IsPath ∧
      ∀ z ∈ p.support, z ≠ u → z ≠ v →
        0 < z.1 ∧ z.1 < M ∧ 0 < z.2 ∧ z.2 < n ∧ ω z = true

theorem crossing_implies_wiredArm {ω : Configuration} {M n r R : ℕ}
    (hnr : n ≤ r) (hrR : r ≤ R) (hRM : R+1 < M)
    (h : HorizontalCrossing ω M n) : WiredArm ω r R := by
  obtain ⟨u,v,hu,huy0,huyn,hv,hvy0,hvyn,p,_,hp⟩ := h
  have hui : u ∈ latticeBox r := by
    simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    omega
  have hvo : v ∉ latticeBox (R+1) := by
    simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    omega
  have hcolors : ∀ z ∈ p.support, wireBoth ω r (R+1) z = true := by
    intro z hz
    by_cases hzu : z = u
    · subst z
      exact wireBoth_inside ω r (R+1) hui
    by_cases hzv : z = v
    · subst z
      exact wireBoth_outside ω r (R+1) hvo
    by_cases hi : z ∈ latticeBox r
    · exact wireBoth_inside ω r (R+1) hi
    by_cases ho : z ∉ latticeBox (R+1)
    · exact wireBoth_outside ω r (R+1) ho
    simp only [wireBoth, hi, ho, or_self, ↓reduceIte]
    exact (hp z hz hzu hzv).2.2.2.2
  apply (wiredConnection_succ_iff_wiredArm ω hrR).mp
  exact ⟨v,⟨wireBoth_inside ω r (R+1) (origin_mem_box r),
    ((filled_box_reachable ω r hui).mono (fillBox_le_wireBoth ω r (R+1))).trans
      (AnnularCollars.reachable_of_colored_walk _ p hcolors)⟩,hvo⟩

theorem horizontalCrossing_congr {ω η : Configuration} {M n : ℕ}
    (heq : ∀ z ∈ rectangle M n, ω z = η z) :
    HorizontalCrossing ω M n ↔ HorizontalCrossing η M n := by
  have hforward : ∀ a b : Configuration,
      (∀ z ∈ rectangle M n, a z=b z) →
      HorizontalCrossing a M n → HorizontalCrossing b M n := by
    intro a b hab
    rintro ⟨u,v,hu,hy0,hyn,hv,hy0',hyn',p,hp,hcol⟩
    refine ⟨u,v,hu,hy0,hyn,hv,hy0',hyn',p,hp,?_⟩
    intro z hz hzu hzv
    obtain ⟨hx0,hxM,hy0,hyN,hblack⟩ := hcol z hz hzu hzv
    refine ⟨hx0,hxM,hy0,hyN,?_⟩
    rw [← hab z (by simp only [rectangle,
      Finset.mem_product,Finset.mem_Icc]; omega)]
    exact hblack
  exact ⟨hforward ω η heq,hforward η ω (fun z hz => (heq z hz).symm)⟩

/-- Critical RSW for axial rectangles, with the source's endpoint-free
convention. The lower cutoff excludes degenerate strips without an
interior row. This is the critical specialization of Nolin's Theorem 2
and equation (3.4); the parameter is a published-result hypothesis. -/
def PublishedCriticalRSW : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ δ : ℝ, 0 < δ ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ D : Finset Site, rectangle (k*n) n ⊆ D →
      δ ≤ probability (fairSites D)
        (fun x => HorizontalCrossing (completeColors D x) (k*n) n)

/-- The radial lower bound is deduced from the literal rectangle event;
its endpoint colors are never silently changed. -/
theorem wiredArm_lower_of_RSW (hsource : PublishedCriticalRSW)
    (k : ℕ) (hk : 2 ≤ k) : ∃ δ : ℝ, 0 < δ ∧
      ∀ (n r R : ℕ), 2 ≤ n → n ≤ r → r ≤ R → R+1 < k*n →
        ∀ D : Finset Site, rectangle (k*n) n ⊆ D →
          δ ≤ probability (fairSites D) (fun x => WiredArm (completeColors D x) r R) := by
  obtain ⟨δ,hδ,hbound⟩ := hsource k hk
  refine ⟨δ,hδ,?_⟩
  intro n r R hn hnr hrR hR D hD
  exact (hbound n hn D hD).trans (CanonicalRadialLaw.probability_mono _
    (fun x hx => crossing_implies_wiredArm hnr hrR hR hx))

#print axioms crossing_implies_wiredArm
#print axioms wiredArm_lower_of_RSW

end ExceptionalTimes.NolinCorridor
