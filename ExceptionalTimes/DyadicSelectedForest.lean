import ExceptionalTimes.DyadicForestStop
import ExceptionalTimes.DimerSelectedDictionary

/-! The proved dyadic polygon forest estimate applied to a literal selected
coefficient of the finite dimer expansion. All exterior and history-coordinate
identifications are exact. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.DyadicSelectedForest

open PairSquareSewing DimerSelectedDictionary DimerLaw DimerExpansion
open CenteredBlocks BlockExpansion CanonicalSpatialProduct

variable {B F : Type*} [Fintype B] [Fintype F]

theorem selected_coefficient_forest_bound
    (hsource : PublishedInvarianceOfDomain)
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily F) (n : ℕ) (hn : T.maxLevel≤n)
    (z : Site) (slot : B × Fin 2 ↪ Site)
    (hdisplacement : ∀ b,slot (b,1)=slot (b,0)+z) (S : Finset B)
    (hspan : ∀ b e f,
      dist (position ((2:ℝ)^n)⁻¹ (slot (b,e))) (position ((2:ℝ)^n)⁻¹ (slot (b,f)))≤
        (T.geometry hsource n z (selectedSlot slot S) (fun i => hdisplacement i.val)).margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop) (hfeature : stop≤T.stop)
    (hsmall : (T.geometry hsource n z (selectedSlot slot S)
      (fun i => hdisplacement i.val)).margin≤cutoff/100)
    (p : B → ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (u : B → History → ℝ) (outer : (F × Bool → Bool) → ℝ)
    (hu : ∀ b,∑ h,u b h=0) (hf : ∀ x,|outer x|≤1)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (D : Finset Site) (hcover : ∀ v∈D,∃ ie,slot ie=v)
    (hD : ∀ a ha,(dimerLifeProbe (T.geometry hsource n z (selectedSlot slot S)
      (fun i => hdisplacement i.val)) cutoff stop hcut a ha).region ⊆ (D : Set Site))
    (hresolution : B₀*((2:ℝ)^n)⁻¹≤8*cutoff)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hpnz : ∀ t,profile t≠0) (hpstop : profile stop=1)
    (hprofile : ∀ t,0<t → t≤stop → 0<profile t)
    (hquasi : ∀ a b,0<a → a<b → b≤stop → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b,0<a → a≤b → b≤stop → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b,B₀*((2:ℝ)^n)⁻¹≤a → 0<a → a≤b → b≤stop → c*(a/b)^g≤α a b) :
    |selectedKernel (fun b h => twoTimeWeight (p b) h.1 h.2) u S
      (fun h => outer (fun qt => T.test n qt.1
        (canonicalBackground slot (pairCoordinates.symm h) qt.2)))|≤
      (∏ i : S,variation (u i.val))*canonicalForestValue
        (T.geometry hsource n z (selectedSlot slot S) (fun i => hdisplacement i.val)) cutoff stop C
        (canonicalForestConstant F C₄ C₃ c C K g) g profile := by
  rw [selected_coefficient_actual_overwrites slot p hp0 hp1 u S
    (fun ω => outer (fun qt => T.test n qt.1 (ω qt.2)))]
  have hw : ∀ i : S,∑ h,u i.val (historyEquiv.symm h)=0 := by
    intro i
    rw [history_sum]
    exact hu i.val
  have h := canonical_dyadic_centered_forest_bound_at_stop hsource hbulkSource hhalfSource
    T n hn z (selectedSlot slot S) (fun i => hdisplacement i.val) slot hspan
    cutoff stop hcut hstop hfeature hsmall p hp0 hp1
    (fun i : S => fun h => u i.val (historyEquiv.symm h)) (fun _ x => outer x) hw
    (fun _ _ => hf _) α profile hfour hthree D hcover hD hresolution
    hg0 hg2 hc hC₃ hC₄ hC hKB hKH hpnz hpstop hprofile hquasi hlower hfourlower
  unfold CenteredBlocks.historyTests DyadicQuadFamily.overwrittenCross CenteredBlocks.slice at h
  simpa only [history_variation] using h

#print axioms selected_coefficient_forest_bound

end ExceptionalTimes.DyadicSelectedForest


