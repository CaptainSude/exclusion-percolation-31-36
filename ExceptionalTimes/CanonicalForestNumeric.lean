import ExceptionalTimes.CanonicalForestBound
import ExceptionalTimes.GenericForestArmWeights

/-! Complete finite centered-response to recorded-forest edge-product
bound for the actual family of axial-box crossings and canonical dimer
law. No global event probability or forest estimate is assumed. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw ForestArmProbability
open ForestArmWeights CenteredBlocks

variable {I J B Q : Type*} [Fintype I] [Fintype J] [Fintype B] [Fintype Q]

noncomputable local instance : DecidableEq (I ⊕ J) := Classical.decEq _

noncomputable def selectedRootEquiv : {v : I ⊕ J // selectedRoot v} ≃ J where
  toFun v := v.property.choose
  invFun j := ⟨Sum.inr j,⟨j,rfl⟩⟩
  left_inv v := Subtype.ext v.property.choose_spec.symm
  right_inv j := by
    have h := (show selectedRoot (Sum.inr j : I ⊕ J) from ⟨j,rfl⟩).choose_spec
    exact (Sum.inr.inj h).symm

theorem selectedRoot_card : Fintype.card {v : I ⊕ J // selectedRoot v}=Fintype.card J :=
  Fintype.card_congr (selectedRootEquiv (I := I) (J := J))

/-- Literal edge product of the root-contracted, threshold-truncated
Kruskal forest of these dimer anchors and marked roots. -/
noncomputable def canonicalForestValue (G : DimerGeometry I J) (cutoff stop C K g : ℝ)
    (profile : ℝ → ℝ) : ℝ :=
  ((K*C^2*256^g)^2*Real.exp (g*(1+4*G.margin/cutoff)))^Fintype.card I *
    (profile cutoff^Fintype.card I /
      ∏ e ∈ (ForestLifeGeometry.recorded selectedRoot (dimerAnchor G) cutoff ⊓
        RootKruskal.threshold (dimerAnchor G) cutoff stop).edgeFinset,
        profile (ForestGeometry.clippedEdgeLength (dimerAnchor G) cutoff e))

theorem canonical_actual_cost_product_bound (G : DimerGeometry I J)
    (cutoff stop C K g : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop)
    (hC : 1≤C) (hK : 1≤K) (hg : 0≤g)
    (α : ℝ → ℝ → ℝ) (hα : ∀ a b, 0≤α a b) (profile : ℝ → ℝ)
    (hpnz : ∀ t, profile t≠0) (hpstop : profile stop=1)
    (hprofile : ∀ t, 0<t → t≤stop → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤stop → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤stop → profile b≤C*(b/a)^g*profile a) :
    (∏ S ∈ ForestTelescope.positiveLives selectedRoot (dimerAnchor G) cutoff stop,
      lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin α S)≤
      canonicalForestValue G cutoff stop C K g profile :=
  by
  have h := GenericForestArmWeights.actual_forest_arm_product (V := I ⊕ J) (Fintype.card I) (Fintype.card J)
    Fintype.card_sum selectedRoot (selectedRoot_card (I := I) (J := J)) (dimerAnchor G)
    hcut hstop G.margin_nonneg hC hK hg α hα profile hpnz hpstop hprofile hquasi hlower
  change _ ≤ canonicalForestValue G cutoff stop C K g profile at h
  exact h

/-- One connected bound from the literal signed kernel under manyLaw to
the explicit edge product of the actual forest. All arm inputs concern
individual static probes; all geometry and spatial factorization are proved. -/
theorem canonical_centered_forest_bound
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
    (hpnz : ∀ t, profile t≠0) (hpstop : profile stop=1)
    (hprofile : ∀ t, 0<t → t≤stop → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤stop → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤stop → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b, B₀*G.mesh≤a → 0<a → a≤b → b≤stop → c*(a/b)^g≤α a b) :
    |(manyLaw p hp0 hp1).expect (fun o => kernel w (fun z =>
      outer o (historyTests (overwrittenCross G.endpoint board (canonicalBackground slot o)) z)))| ≤
      (∏ i, variation (w i))*canonicalForestValue G cutoff stop C
        (canonicalForestConstant Q C₄ C₃ c C K g) g profile := by
  let β := positiveCanonicalArmRatio Q C₄ C₃ c C K g profile
  have hlocal (a : DimerLife G cutoff stop) :
      probability (manyLaw p hp0 hp1)
        (fun z => DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot z)) ≤
        lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin β a.val :=
    (canonical_life_probability_le_cost G slot cutoff stop hcut hstop α profile hfour hthree
      p hp0 hp1 D hcover board a (hD a) hresolution hg0 hg2 hc hC₃ hC₄ hC hKB hKH
      hprofile hquasi hlower hfourlower).trans
        (lifeCost_positiveCanonicalArmRatio G cutoff stop C₄ C₃ c C K g profile a.val)
  have hproduct :
      (∏ a, probability (manyLaw p hp0 hp1)
        (fun z => DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot z))) ≤
      ∏ S ∈ ForestTelescope.positiveLives selectedRoot (dimerAnchor G) cutoff stop,
        lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin β S := by
    calc
      _ ≤ ∏ a : DimerLife G cutoff stop,
          lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin β a.val :=
        Finset.prod_le_prod₀ (fun _ _ => probability_nonneg _ _) (fun a _ => hlocal a)
      _ = _ := Finset.prod_coe_sort _ _
  have hforest := canonical_actual_cost_product_bound G cutoff stop C
    (canonicalForestConstant Q C₄ C₃ c C K g) g hcut hstop hC
    (canonicalForestConstant_ge_one C₄ C₃ c C K g) hg0 β
    (positiveCanonicalArmRatio_nonneg C₄ C₃ c C K g profile) profile hpnz hpstop hprofile
    (fun a b ha hab hbs => positiveCanonicalArmRatio_quasi C₄ C₃ c C K g profile
      (hprofile a ha (hab.le.trans hbs)) (hprofile b (ha.trans hab) hbs)) hlower
  have hv : 0≤∏ i, variation (w i) :=
    Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun z _ => abs_nonneg (w i z)))
  exact (canonical_centered_life_product hbulkSource hhalfSource G slot hspan cutoff stop hcut hsmall
    board hboard hscale corner hcorner p hp0 hp1 w outer hw hf).trans
    (mul_le_mul_of_nonneg_left (hproduct.trans hforest) hv)

#print axioms canonical_centered_forest_bound

end ExceptionalTimes.PairSquareSewing



