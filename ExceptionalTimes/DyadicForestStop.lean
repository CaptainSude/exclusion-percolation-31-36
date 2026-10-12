import ExceptionalTimes.DyadicForestBound

/-! The actual canonical centered response for a finite family of fixed
physical dyadic-grid quads. Every geometric premise of the polygon forest
theorem is supplied by the exact dyadic presentation. The literal closed-cell
crossing tests are retained on the left hand side. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw ForestArmProbability
open ForestArmWeights CenteredBlocks

variable {I B F : Type*} [Fintype I] [Fintype B] [Fintype F]

theorem canonical_dyadic_centered_forest_bound_at_stop
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
    (hfour : PublishedFourArmBound B₀ C₄ α)
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
  exact canonical_polygon_centered_forest_bound hbulkSource hhalfSource
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

#print axioms canonical_dyadic_centered_forest_bound_at_stop

end ExceptionalTimes.PairSquareSewing


