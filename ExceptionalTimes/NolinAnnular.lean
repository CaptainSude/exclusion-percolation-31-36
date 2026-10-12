import ExceptionalTimes.NolinCorridor
import ExceptionalTimes.HexCutTrimming

/-! Literal source annular crossings and the upper-bound dictionary.
Both source endpoints are uncolored. The wired event implies this
source event by actual last-departure/first-arrival path trimming. -/

namespace ExceptionalTimes.NolinCorridor

open HoleFilling EnvironmentVariance ProbeProduct PairSquareSewing
open scoped Classical

def axialRadius (z : Site) : ℤ := max |z.1| |z.2|

theorem axialRadius_le_iff (z : Site) (r : ℕ) :
    axialRadius z ≤ r ↔ z ∈ latticeBox r := by
  simp [axialRadius,abs_le,latticeBox]

theorem axialRadius_step {u v : Site} (h : TriangularAdj u v) :
    axialRadius v ≤ axialRadius u + 1 := by
  have hx := abs_le.mp (show |u.1| ≤ axialRadius u from le_max_left _ _)
  have hy := abs_le.mp (show |u.2| ≤ axialRadius u from le_max_right _ _)
  simp only [axialRadius] at hx hy
  simp only [axialRadius,max_le_iff,abs_le]
  unfold TriangularAdj at h
  omega

/-- Nolin's annular crossing convention (section 2.1): a simple path
between the two exact boundary levels, with only interior sites black.
The interior also avoids both boundary levels. -/
def AnnularCrossing (ω : Configuration) (r R : ℕ) : Prop :=
  ∃ u, axialRadius u = r ∧ ∃ v, axialRadius v = R ∧
    ∃ p : triangularGraph.Walk u v, p.IsPath ∧
      ∀ z ∈ p.support, z ≠ u → z ≠ v →
        (r : ℤ) < axialRadius z ∧ axialRadius z < R ∧ ω z = true

theorem wiredArm_implies_source_annular {ω : Configuration} {r R : ℕ}
    (hrR : r < R) (h : WiredArm ω r R) : AnnularCrossing ω r R := by
  obtain ⟨u,hu,v,hv,p,hp,_,hcol,_⟩ := h
  have hur : axialRadius u ≤ r := (axialRadius_le_iff u r).mpr hu
  have hvR : (R : ℤ) ≤ axialRadius v := by
    have hnot : ¬axialRadius v ≤ R := fun h => hv ((axialRadius_le_iff v R).mp h)
    omega
  obtain ⟨x,hx,y,hy,q,hq,hsub,hinside,hinner,houter⟩ :=
    trim_path_integer_levels axialRadius axialRadius_step r R (by exact_mod_cast hrR)
      p hp hur hvR
  refine ⟨x,hx,y,hy,q,hq,?_⟩
  intro z hz hzx hzy
  have hbounds := hinside z hz
  have hneqr : axialRadius z ≠ r := fun he => hzx (hinner z hz he)
  have hneqR : axialRadius z ≠ R := fun he => hzy (houter z hz he)
  have hzu : z ≠ u := by
    intro h
    subst z
    omega
  exact ⟨by omega,by omega,(hcol z (hsub.support_subset hz) hzu).2⟩

theorem annularCrossing_congr {ω η : Configuration} {r R : ℕ}
    (heq : ∀ z ∈ latticeBox R, ω z=η z) :
    AnnularCrossing ω r R ↔ AnnularCrossing η r R := by
  have hforward : ∀ a b : Configuration,
      (∀ z ∈ latticeBox R, a z=b z) →
      AnnularCrossing a r R → AnnularCrossing b r R := by
    intro a b hab
    rintro ⟨u,hu,v,hv,p,hp,hcol⟩
    refine ⟨u,hu,v,hv,p,hp,?_⟩
    intro z hz hzu hzv
    obtain ⟨hi,ho,hc⟩ := hcol z hz hzu hzv
    exact ⟨hi,ho,(hab z ((axialRadius_le_iff z R).mp ho.le)).symm.trans hc⟩
  exact ⟨hforward ω η heq,hforward η ω (fun z hz => (heq z hz).symm)⟩

/-- The classical uniform polynomial one-arm upper bound, in the
source's literal square-annulus convention. Source02 lemma2.1 cites
Nolin's RSW/arm separation inputs for this statement. The cutoff and
exponent remain explicit and must be positive in applications. -/
def PublishedAnnularOneArmUpper (B₀ : ℕ) (C β : ℝ) : Prop :=
  ∀ r R : ℕ, B₀ ≤ r → r < R → ∀ D : Finset Site, latticeBox R ⊆ D →
    probability (fairSites D) (fun x => AnnularCrossing (completeColors D x) r R) ≤
      C*((r : ℝ)/R)^β

theorem wiredArm_upper_of_published {B₀ : ℕ} {C β : ℝ}
    (hsource : PublishedAnnularOneArmUpper B₀ C β)
    {r R : ℕ} (hr : B₀ ≤ r) (hrR : r < R)
    (D : Finset Site) (hD : latticeBox R ⊆ D) :
    probability (fairSites D) (fun x => WiredArm (completeColors D x) r R) ≤
      C*((r : ℝ)/R)^β :=
  (CanonicalRadialLaw.probability_mono _
    (fun _ h => wiredArm_implies_source_annular hrR h)).trans (hsource r R hr hrR D hD)

#print axioms wiredArm_implies_source_annular
#print axioms wiredArm_upper_of_published

end ExceptionalTimes.NolinCorridor
