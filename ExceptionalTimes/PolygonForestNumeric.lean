import ExceptionalTimes.CanonicalForestNumeric
import ExceptionalTimes.PolygonForestProbability
import ExceptionalTimes.PolygonLifeCost

/-! A connected literal polygon centered-response bound under the actual
canonical law, ending at the edge product of the actual recorded forest.
All boundary segments and their marked endpoints remain explicit. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw ForestArmProbability
open ForestArmWeights CenteredBlocks

variable {I J B Q : Type*} [Fintype I] [Fintype J] [Fintype B] [Fintype Q]

noncomputable local instance : DecidableEq (I ⊕ J) := Classical.decEq _

theorem canonical_polygon_centered_forest_bound
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f, dist (position G.mesh (slot (b,e))) (position G.mesh (slot (b,f)))≤G.margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop) (hsmall : G.margin≤cutoff/100)
    (quads : Q → PolygonQuad) (E : Q → Type*)
    (A : ∀ q, AxialPolygonPresentation (quads q) (E q)) (δ : Q → ℝ)
    (hscale : ∀ q, 6*(stop/8)<G.mesh*δ q)
    (hparallel : ∀ q i j, ((A q).edge i).horizontal=((A q).edge j).horizontal →
      ((A q).edge i).level≠((A q).edge j).level →
        δ q≤|((A q).edge i).level-((A q).edge j).level|)
    (vertex : ∀ q, E q → Bool → J)
    (hvertex : ∀ q i b, G.root (vertex q i b)=axialPhysical G.mesh
      (if b then ((A q).edge i).last else ((A q).edge i).first))
    (hinteger : ∀ q i, ∃ level : ℤ, ((A q).edge i).level=(level:ℝ))
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (w : I → (Bool → CenteredBlocks.PairColor) → ℝ)
    (outer : ((B → Color) × (B → Color)) → (Q × Bool → Bool) → ℝ)
    (hw : ∀ i, ∑ z, w i z=0)
    (hf : ∀ o z, |outer o (historyTests (polygonOverwrittenCross G.endpoint quads (canonicalBackground slot o)) z)|≤1)
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
      outer o (historyTests (polygonOverwrittenCross G.endpoint quads (canonicalBackground slot o)) z)))| ≤
      (∏ i, variation (w i))*canonicalForestValue G cutoff stop C
        (canonicalForestConstant Q C₄ C₃ c C K g) g profile := by
  obtain ⟨choice,hresponse⟩ := canonical_polygon_centered_life_product hbulkSource hhalfSource
    G slot hspan cutoff stop hcut hsmall quads E A δ hscale hparallel vertex hvertex hinteger
    p hp0 hp1 w outer hw hf
  let β := positiveCanonicalArmRatio Q C₄ C₃ c C K g profile
  have hlocal (a : DimerLife G cutoff stop) :
      probability (manyLaw p hp0 hp1)
        (fun z => PolygonLifeEvent choice a (canonicalBackground slot z)) ≤
        lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin β a.val :=
    (canonical_polygon_life_probability_le_cost G slot cutoff stop hcut hstop α profile hfour hthree
      p hp0 hp1 D hcover choice a (hD a) hresolution hg0 hg2 hc hC₃ hC₄ hC hKB hKH
      hprofile hquasi hlower hfourlower).trans
        (lifeCost_positiveCanonicalArmRatio G cutoff stop C₄ C₃ c C K g profile a.val)
  have hproduct :
      (∏ a, probability (manyLaw p hp0 hp1)
        (fun z => PolygonLifeEvent choice a (canonicalBackground slot z))) ≤
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
  exact hresponse.trans (mul_le_mul_of_nonneg_left (hproduct.trans hforest) hv)

#print axioms canonical_polygon_centered_forest_bound

end ExceptionalTimes.PairSquareSewing



