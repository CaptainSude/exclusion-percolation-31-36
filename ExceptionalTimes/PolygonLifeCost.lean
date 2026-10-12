import ExceptionalTimes.PolygonCanonicalProbability
import ExceptionalTimes.PolygonLifeChoice
import ExceptionalTimes.CanonicalLifeCost

/-! Actual arbitrary-polygon probe choices have precisely the same
separated life cost used by the proved rooted-forest charging theorem. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw ForestArmProbability
open ForestArmWeights

variable {I J B Q : Type*} [Fintype I] [Fintype J] [Fintype B] [Fintype Q]

theorem canonical_polygon_life_probability_le_cost
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v)
    (choice : PolygonLifeChoiceAssignment G cutoff stop hcut Q) (a : DimerLife G cutoff stop)
    (hD : ∀ ha, (dimerLifeProbe G cutoff stop hcut a ha).region ⊆ (D : Set Site))
    (hresolution : B₀*G.mesh≤8*cutoff)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hprofile : ∀ t, 0<t → t≤stop → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤stop → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤stop → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b, B₀*G.mesh≤a → 0<a → a≤b → b≤stop → c*(a/b)^g≤α a b) :
    probability (manyLaw p hp0 hp1)
      (fun z => PolygonLifeEvent choice a (canonicalBackground slot z)) ≤
      lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin
        (canonicalArmRatio Q C₄ C₃ c C K g profile) a.val := by
  change _ ≤ ArmEnlargement.separatedArmCost _ (lifeInner G cutoff stop a) (lifeOuter G cutoff stop a)
  by_cases ha : LifeProbeActive G cutoff stop a
  · have ha' : 4*lifeInner G cutoff stop a<lifeOuter G cutoff stop a := ha
    rw [ArmEnlargement.separatedArmCost,ite_eq_left ha']
    have hevent : probability (manyLaw p hp0 hp1)
        (fun z => PolygonLifeEvent choice a (canonicalBackground slot z)) =
        probability (manyLaw p hp0 hp1) (fun z => ∃ q t,
          (choice a ha q).event
            (canonicalBackground slot z t)) := by
      apply probability_congr
      exact fun _ => ⟨fun h => h ha,fun h _ => h⟩
    rw [hevent]
    have hlife := (ForestTelescope.positiveLives_spec selectedRoot (dimerAnchor G) cutoff stop a.property).1
    have hb := KruskalLives.cutoff_le_birth hlife
    have hd := KruskalLives.death_le_stop hlife
    have hmax := le_max_left (KruskalLives.birth selectedRoot (dimerAnchor G) cutoff stop a.val)
      (ForestProbes.span selectedRoot (dimerAnchor G) cutoff a.val+2*G.margin)
    have hr : B₀*(dimerLifeProbe G cutoff stop hcut a ha).mesh≤
        (dimerLifeProbe G cutoff stop hcut a ha).innerRadius := by
      change B₀*G.mesh≤8*max _ _
      linarith
    have hR : (dimerLifeProbe G cutoff stop hcut a ha).outerRadius≤stop := by
      change KruskalLives.death selectedRoot (dimerAnchor G) cutoff stop a.val/8≤stop
      linarith
    exact canonical_polygonProbe_union_bound α profile hfour hthree p hp0 hp1 slot D hcover
      (dimerLifeProbe G cutoff stop hcut a ha) (choice a ha) (hD ha) hr hg0 hg2 hc hC₃ hC₄ hC hKB hKH
      (fun t ht hts => hprofile t ht (hts.trans hR))
      (fun r R hr hrR hRs => hquasi r R hr hrR (hRs.trans hR))
      (fun r R hr hrR hRs => hlower r R hr hrR (hRs.trans hR))
      (fun r R hm hr hrR hRs => hfourlower r R hm hr hrR (hRs.trans hR))
  · have ha' : ¬4*lifeInner G cutoff stop a<lifeOuter G cutoff stop a := ha
    rw [ArmEnlargement.separatedArmCost,ite_eq_right ha']
    exact probability_le_one _ _

theorem canonical_polygon_life_probability_product_le_cost
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v) (choice : PolygonLifeChoiceAssignment G cutoff stop hcut Q)
    (hD : ∀ a ha, (dimerLifeProbe G cutoff stop hcut a ha).region ⊆ (D : Set Site))
    (hresolution : B₀*G.mesh≤8*cutoff)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hprofile : ∀ t, 0<t → t≤stop → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤stop → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤stop → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b, B₀*G.mesh≤a → 0<a → a≤b → b≤stop → c*(a/b)^g≤α a b) :
    (∏ a, probability (manyLaw p hp0 hp1)
      (fun z => PolygonLifeEvent choice a (canonicalBackground slot z))) ≤
      ∏ S ∈ ForestTelescope.positiveLives selectedRoot (dimerAnchor G) cutoff stop,
        lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin
          (canonicalArmRatio Q C₄ C₃ c C K g profile) S := by
  calc
    _ ≤ ∏ a : DimerLife G cutoff stop,
        lifeCost selectedRoot (dimerAnchor G) cutoff stop G.margin
          (canonicalArmRatio Q C₄ C₃ c C K g profile) a.val :=
      Finset.prod_le_prod₀ (fun _ _ => probability_nonneg _ _) (fun a _ =>
        canonical_polygon_life_probability_le_cost G slot cutoff stop hcut hstop α profile hfour hthree
          p hp0 hp1 D hcover choice a (hD a) hresolution hg0 hg2 hc hC₃ hC₄ hC hKB hKH
          hprofile hquasi hlower hfourlower)
    _ = _ := Finset.prod_coe_sort _ _

#print axioms canonical_polygon_life_probability_product_le_cost

end ExceptionalTimes.PairSquareSewing
