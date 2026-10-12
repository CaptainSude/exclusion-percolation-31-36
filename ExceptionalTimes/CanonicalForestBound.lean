import ExceptionalTimes.CanonicalForestProbability
import ExceptionalTimes.CanonicalLifeCost

/-! The actual centered dimer kernel, the canonical two-time exterior,
literal axial-box arm necessity, and published static arm estimates are
connected to the exact life-cost product of the constructed forest. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw ForestArmProbability
open ForestArmWeights CenteredBlocks

variable {I J B Q : Type*} [Fintype I] [Fintype J] [Fintype B] [Fintype Q]

omit [Fintype I] [Fintype J] in
/-- With two endpoints, the anchor bound also bounds every endpoint pair.
For displacedDimerGeometry this is max(mesh,mesh*‖embedding z‖), for any z. -/
theorem DimerGeometry.pairwise_bound (G : DimerGeometry I J) (i : I) (e f : Fin 2) :
    dist (position G.mesh (G.endpoint (i,e))) (position G.mesh (G.endpoint (i,f)))≤G.margin := by
  fin_cases e <;> fin_cases f
  · change dist (position G.mesh (G.endpoint (i,0))) (position G.mesh (G.endpoint (i,0)))≤_
    simpa only [dist_self] using G.margin_nonneg
  · exact G.endpoint_bound i 1
  · change dist (position G.mesh (G.endpoint (i,1))) (position G.mesh (G.endpoint (i,0)))≤_
    rw [dist_comm]
    exact G.endpoint_bound i 1
  · change dist (position G.mesh (G.endpoint (i,1))) (position G.mesh (G.endpoint (i,1)))≤_
    simpa only [dist_self] using G.margin_nonneg

theorem canonical_centered_actual_life_cost
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f, dist (position G.mesh (slot (b,e))) (position G.mesh (slot (b,f)))≤G.margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop) (hsmall : G.margin≤cutoff/100)
    (board : Q → ℕ) (hboard : ∀ q, 0<board q) (hscale : ∀ q, 3*(stop/8)<G.mesh*board q)
    (corner : Q → Bool → Bool → J)
    (hcorner : ∀ q s t, G.root (corner q s t)=axialPhysical G.mesh
      (signedSide (board q) s,signedSide (board q) t))
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (w : I → (Bool → CenteredBlocks.PairColor) → ℝ)
    (outer : ((B → Color) × (B → Color)) → (Q × Bool → Bool) → ℝ)
    (hw : ∀ i, ∑ z, w i z=0)
    (hf : ∀ o z, |outer o (historyTests (overwrittenCross G.endpoint board (canonicalBackground slot o)) z)|≤1)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v)
    (hD : ∀ a ha, (dimerLifeProbe G cutoff stop hcut a ha).region ⊆ (D : Set Site))
    (hresolution : B₀*G.mesh≤8*cutoff)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hprofile : ∀ t, 0<t → t≤stop → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤stop → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤stop → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b, B₀*G.mesh≤a → 0<a → a≤b → b≤stop → c*(a/b)^g≤α a b) :
    |(manyLaw p hp0 hp1).expect (fun o => kernel w (fun z =>
      outer o (historyTests (overwrittenCross G.endpoint board (canonicalBackground slot o)) z)))| ≤
      (∏ i, variation (w i))*
        ∏ S ∈ ForestTelescope.positiveLives selectedRoot (dimerAnchor G) cutoff stop,
          lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin
            (canonicalArmRatio Q C₄ C₃ c C K g profile) S := by
  have hv : 0≤∏ i, variation (w i) :=
    Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun z _ => abs_nonneg (w i z)))
  exact (canonical_centered_life_product hbulkSource hhalfSource G slot hspan cutoff stop hcut hsmall
    board hboard hscale corner hcorner p hp0 hp1 w outer hw hf).trans
    (mul_le_mul_of_nonneg_left
      (canonical_life_probability_product_le_cost G slot cutoff stop hcut hstop α profile hfour hthree
        p hp0 hp1 D hcover board hD hresolution hg0 hg2 hc hC₃ hC₄ hC hKB hKH
        hprofile hquasi hlower hfourlower) hv)

/-- Extension outside the geometric range is explicitly nonnegative;
inside that range this retains the actual finite-choice cost. -/
noncomputable def positiveCanonicalArmRatio (Q : Type*) [Fintype Q]
    (C₄ C₃ c C K g : ℝ) (profile : ℝ → ℝ) (r R : ℝ) : ℝ :=
  max 0 (canonicalArmRatio Q C₄ C₃ c C K g profile r R)

noncomputable def canonicalForestConstant (Q : Type*) [Fintype Q]
    (C₄ C₃ c C K g : ℝ) : ℝ :=
  max 1 ((Fintype.card (Q × Bool) : ℝ)*fullProbeConstant C₄ C₃ c C K g)

theorem positiveCanonicalArmRatio_nonneg (C₄ C₃ c C K g : ℝ) (profile : ℝ → ℝ) (r R : ℝ) :
    0≤positiveCanonicalArmRatio Q C₄ C₃ c C K g profile r R := le_max_left _ _

theorem canonicalForestConstant_ge_one (C₄ C₃ c C K g : ℝ) :
    1≤canonicalForestConstant Q C₄ C₃ c C K g := le_max_left _ _

theorem positiveCanonicalArmRatio_quasi (C₄ C₃ c C K g : ℝ) (profile : ℝ → ℝ)
    {r R : ℝ} (hr : 0<profile r) (hR : 0<profile R) :
    positiveCanonicalArmRatio Q C₄ C₃ c C K g profile r R ≤
      canonicalForestConstant Q C₄ C₃ c C K g*(profile r/profile R) := by
  have hratio : 0≤profile r/profile R := div_nonneg hr.le hR.le
  apply max_le
  · exact mul_nonneg ((by norm_num : (0:ℝ)≤1).trans (canonicalForestConstant_ge_one _ _ _ _ _ _)) hratio
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hratio

theorem lifeCost_positiveCanonicalArmRatio (G : DimerGeometry I J)
    (cutoff stop : ℝ) (C₄ C₃ c C K g : ℝ) (profile : ℝ → ℝ) (S : Set (I ⊕ J)) :
    lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin
        (canonicalArmRatio Q C₄ C₃ c C K g profile) S ≤
      lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin
        (positiveCanonicalArmRatio Q C₄ C₃ c C K g profile) S := by
  unfold lifeCost ArmEnlargement.separatedArmCost
  split_ifs
  · exact le_max_right _ _
  · rfl

#print axioms canonical_centered_actual_life_cost
#print axioms positiveCanonicalArmRatio_quasi

end ExceptionalTimes.PairSquareSewing
