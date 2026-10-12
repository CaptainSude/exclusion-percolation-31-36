import ExceptionalTimes.FixedMeshForest
import ExceptionalTimes.DimerBaseField

/-! The literal selected expansion kernel at its static base is bounded
using the fixed-mesh polygon forest theorem. A separate exterior cover
supplies every annular probe, even for insertions near the original box. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.FixedMeshSelectedForest

open PairSquareSewing DimerSelectedDictionary DimerBaseField DimerLaw DimerExpansion
open CenteredBlocks BlockExpansion CanonicalSpatialProduct

variable {B E F : Type*} [Fintype B] [Fintype E] [Fintype F]

noncomputable def testSupport (hsource : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily F) (n : ℕ) : Finset Site :=
  polygonFamilySupport (fun i => (T.grid i).meshPolygon hsource n)

theorem test_local (hsource : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily F) (n : ℕ) (hn : T.maxLevel≤n)
    (ω η : TwoTimeConfiguration) (hag : ∀ t v,v∈testSupport hsource T n → ω t v=η t v) :
    (fun qt : F×Bool => T.test n qt.1 (ω qt.2))=
      fun qt : F×Bool => T.test n qt.1 (η qt.2) := by
  funext qt
  rw [T.test_eq hsource n hn,T.test_eq hsource n hn]
  apply PolygonQuad.test_congr
  intro v hv
  exact hag qt.2 v ((mem_polygonFamilySupport _ v).mpr
    ⟨qt.1,((T.grid qt.1).meshPolygon hsource n).mem_support v |>.mp hv⟩)

theorem selected_base_forest_bound
    (hsource : PublishedInvarianceOfDomain)
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily F) (n : ℕ) (hn : T.maxLevel≤n)
    (z : Site) (slot : B × Fin 2 ↪ Site) (exterior : E × Fin 2 ↪ Site)
    (hdisplacement : ∀ b,slot (b,1)=slot (b,0)+z) (S : Finset B)
    (hspan : ∀ b e f,
      dist (position ((2:ℝ)^n)⁻¹ (exterior (b,e))) (position ((2:ℝ)^n)⁻¹ (exterior (b,f)))≤
        (T.geometry hsource n z (selectedSlot slot S) (fun i => hdisplacement i.val)).margin)
    (hcover : ∀ v∈testSupport hsource T n,∃ be,slot be=v)
    (hext : ∀ v∈testSupport hsource T n,∃ be,exterior be=v)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hstop : cutoff≤stop) (hfeature : stop≤T.stop)
    (hsmall : (T.geometry hsource n z (selectedSlot slot S)
      (fun i => hdisplacement i.val)).margin≤cutoff/100)
    (u : B → History → ℝ) (outer : (F × Bool → Bool) → ℝ)
    (hu : ∀ b,∑ h,u b h=0) (hf : ∀ x,|outer x|≤1)
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt ((2:ℝ)^n)⁻¹ B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (D : Finset Site) (hDcover : ∀ v∈D,∃ ie,exterior ie=v)
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
    |selectedKernel (fun _ => base) u S
      (fun h => outer (fun qt => T.test n qt.1
        (canonicalBackground slot (pairCoordinates.symm h) qt.2)))|≤
      (∏ i : S,variation (u i.val))*canonicalForestValue
        (T.geometry hsource n z (selectedSlot slot S) (fun i => hdisplacement i.val)) cutoff stop C
        (canonicalForestConstant F C₄ C₃ c C K g) g profile := by
  rw [selected_coefficient_extended_base slot exterior (testSupport hsource T n) hcover hext u S
    (fun ω => outer (fun qt => T.test n qt.1 (ω qt.2)))
    (fun ω η hag => congrArg outer (test_local hsource T n hn ω η hag))]
  have hw : ∀ i : S,∑ h,u i.val (historyEquiv.symm h)=0 := by
    intro i
    rw [history_sum]
    exact hu i.val
  have h := canonical_dyadic_centered_forest_bound_at_stop_fixed_mesh hsource hbulkSource hhalfSource
    T n hn z (selectedSlot slot S) (fun i => hdisplacement i.val) exterior hspan
    cutoff stop hcut hstop hfeature hsmall (fun _ => 0) (fun _ => le_rfl) (fun _ => by norm_num)
    (fun i : S => fun h => u i.val (historyEquiv.symm h)) (fun _ x => outer x) hw
    (fun _ _ => hf _) α profile hfour hthree D hDcover hD hresolution
    hg0 hg2 hc hC₃ hC₄ hC hKB hKH hpnz hpstop hprofile hquasi hlower hfourlower
  unfold CenteredBlocks.historyTests DyadicQuadFamily.overwrittenCross CenteredBlocks.slice at h
  simpa only [history_variation] using h

#print axioms selected_base_forest_bound
end ExceptionalTimes.FixedMeshSelectedForest
