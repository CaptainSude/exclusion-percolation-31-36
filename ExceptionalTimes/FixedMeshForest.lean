import ExceptionalTimes.FixedMeshArmBounds

/-! The actual polygon-life and recorded-forest bound at one fixed mesh.
Its dyadic specialization accepts the ordinary profile at mesh 2^(-n)
only. No single arm profile is imposed across distinct lattices. -/
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.PairSquareSewing
noncomputable section
open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw ForestArmProbability
open ForestArmWeights CenteredBlocks
variable {I J B Q F : Type*} [Fintype I] [Fintype J] [Fintype B] [Fintype Q] [Fintype F]
noncomputable local instance : DecidableEq (I⊕J) := Classical.decEq _

theorem canonical_polygon_life_probability_le_cost_at_mesh
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt G.mesh B₀ C₄ α)
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
    exact canonical_polygonProbe_union_bound_at_mesh α profile hfour hthree p hp0 hp1 slot D hcover
      (dimerLifeProbe G cutoff stop hcut a ha) rfl (choice a ha) (hD ha) hr hg0 hg2 hc hC₃ hC₄ hC hKB hKH
      (fun t ht hts => hprofile t ht (hts.trans hR))
      (fun r R hr hrR hRs => hquasi r R hr hrR (hRs.trans hR))
      (fun r R hr hrR hRs => hlower r R hr hrR (hRs.trans hR))
      (fun r R hm hr hrR hRs => hfourlower r R hm hr hrR (hRs.trans hR))
  · have ha' : ¬4*lifeInner G cutoff stop a<lifeOuter G cutoff stop a := ha
    rw [ArmEnlargement.separatedArmCost,ite_eq_right ha']
    exact probability_le_one _ _

theorem canonical_polygon_life_probability_product_le_cost_at_mesh
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt G.mesh B₀ C₄ α)
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
        canonical_polygon_life_probability_le_cost_at_mesh G slot cutoff stop hcut hstop α profile hfour hthree
          p hp0 hp1 D hcover choice a (hD a) hresolution hg0 hg2 hc hC₃ hC₄ hC hKB hKH
          hprofile hquasi hlower hfourlower)
    _ = _ := Finset.prod_coe_sort _ _

theorem canonical_polygon_centered_forest_bound_at_mesh
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
    (hfour : PublishedFourArmBoundAt G.mesh B₀ C₄ α)
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
    (canonical_polygon_life_probability_le_cost_at_mesh G slot cutoff stop hcut hstop α profile hfour hthree
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

theorem canonical_dyadic_centered_forest_bound_at_stop_fixed_mesh
    (hsource : PublishedInvarianceOfDomain)
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily F) (n : ℕ) (hn : T.maxLevel≤n)
    (z : Site) (endpoint : I × Fin 2 ↪ Site)
    (hdisplacement : ∀ i, endpoint (i,1)=endpoint (i,0)+z)
    (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f,
      dist (position ((2:ℝ)^n)⁻¹ (slot (b,e))) (position ((2:ℝ)^n)⁻¹ (slot (b,f)))≤
        (T.geometry hsource n z endpoint hdisplacement).margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop) (hfeature : stop≤T.stop)
    (hsmall : (T.geometry hsource n z endpoint hdisplacement).margin≤cutoff/100)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (w : I → (Bool → CenteredBlocks.PairColor) → ℝ)
    (outer : ((B → Color) × (B → Color)) → (F × Bool → Bool) → ℝ)
    (hw : ∀ i, ∑ a, w i a=0)
    (hf : ∀ o a, |outer o (historyTests
      (T.overwrittenCross n endpoint (canonicalBackground slot o)) a)|≤1)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt ((2:ℝ)^n)⁻¹ B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v)
    (hD : ∀ a ha, (dimerLifeProbe (T.geometry hsource n z endpoint hdisplacement)
      cutoff stop hcut a ha).region ⊆ (D : Set Site))
    (hresolution : B₀*((2:ℝ)^n)⁻¹≤8*cutoff)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hpnz : ∀ t, profile t≠0) (hpstop : profile stop=1)
    (hprofile : ∀ t, 0<t → t≤stop → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤stop → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤stop → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b, B₀*((2:ℝ)^n)⁻¹≤a → 0<a → a≤b → b≤stop →
      c*(a/b)^g≤α a b) :
    |(manyLaw p hp0 hp1).expect (fun o => kernel w (fun a =>
      outer o (historyTests (T.overwrittenCross n endpoint (canonicalBackground slot o)) a)))| ≤
      (∏ i, variation (w i))*canonicalForestValue
        (T.geometry hsource n z endpoint hdisplacement) cutoff stop C
        (canonicalForestConstant F C₄ C₃ c C K g) g profile := by
  simp_rw [T.overwrittenCross_eq hsource n hn] at hf ⊢
  exact canonical_polygon_centered_forest_bound_at_mesh hbulkSource hhalfSource
    (T.geometry hsource n z endpoint hdisplacement) slot hspan cutoff stop hcut hstop hsmall
    (fun i => (T.grid i).meshPolygon hsource n) (fun i => ↥(T.Edges i))
    (fun i => (T.grid i).meshPresentation hsource n) (fun i => (T.grid i).meshSpacing n)
    (fun i => by
      change 6*(stop/8)<((2:ℝ)^n)⁻¹*(T.grid i).meshSpacing n
      have h := T.feature_scale n i
      linarith)
    (fun i e f _ hne => T.parallel_separation hsource n i e f hne)
    T.vertex (T.geometry_vertex hsource n z endpoint hdisplacement)
    (T.integer_levels hsource n hn)
    p hp0 hp1 w outer hw hf α profile hfour hthree D hcover hD hresolution
    hg0 hg2 hc hC₃ hC₄ hC hKB hKH hpnz hpstop hprofile hquasi hlower hfourlower
#print axioms canonical_polygon_centered_forest_bound_at_mesh
#print axioms canonical_dyadic_centered_forest_bound_at_stop_fixed_mesh
end
end ExceptionalTimes.PairSquareSewing
