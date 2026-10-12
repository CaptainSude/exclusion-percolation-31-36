import ExceptionalTimes.WordForestGeometry
import ExceptionalTimes.FiniteForestExterior
import ExceptionalTimes.CircularStaticProfile

/-! The published ordinary circular-arm estimates give the actual selected
geometry bound. Every exterior sample is constructed from the finite test
support and the actual life-probe disks; no coverage or law input remains. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.CircularForestGeometry
noncomputable section
open PairSquareSewing FixedMeshSelectedForest DimerSelectedDictionary
open DimerExpansion CenteredBlocks BlockExpansion CanonicalSpatialProduct
open CircularStaticProfile ForestGeometryEnvelope NormalizedForestProfile
open WordForestGeometry FiniteForestExterior SelectedPerturbation

variable {A F : Type*} [Fintype A] [Fintype F]

theorem circular_envelope_geometryBound
    (hplane : PublishedInvarianceOfDomain)
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (T : DyadicQuadFamily F) (n : ℕ) (hn : T.maxLevel≤n)
    (z : Site) (slot : A×Fin 2 ↪ Site)
    (hdisp : ∀ i,slot (i,1)=slot (i,0)+z)
    (hcover : ∀ v∈testSupport hplane T n,∃ ie,slot ie=v)
    {B C₄ C₃ Q c g : ℝ} (hcircle : PublishedCircularArmInputs B C₄ Q c g)
    (hthree : PublishedHalfThreeArmBound B C₃) (hcC₃ : c≤C₃)
    (κ stop D : ℝ) (hκ : B≤κ) (hκstop : κ*((2:ℝ)^n)⁻¹≤stop)
    (hstop : 4*stop<1) (hfeature : stop≤T.stop)
    (hsmall : ∀ S : Finset A,
      (T.geometry hplane n z (selectedSlot slot S) (fun i => hdisp i.val)).margin≤
        (κ*((2:ℝ)^n)⁻¹)/100)
    (hcutRadius : ∀ S : Finset A,S.Nonempty →
      κ*((2:ℝ)^n)⁻¹≤OptimizedForestStop.radius stop D S.card)
    (outer : (F×Bool→Bool)→ℝ) (hf : ∀ x,|outer x|≤1) :
    GeometryBound (fun _ => ActualProductTransfer.baseLaw)
      (fun h => outer (fun qt => T.test n qt.1
        (canonicalBackground slot (pairCoordinates.symm h) qt.2)))
      (envelope (fun S => T.geometry hplane n z (selectedSlot slot S) (fun i => hdisp i.val))
        (κ*((2:ℝ)^n)⁻¹) stop D (max 1 (Q/c))
        (canonicalForestConstant F C₄ C₃ c (max 1 (Q/c)) Q g) g
        (profile ((2:ℝ)^n)⁻¹ (by positivity) B stop)) := by
  let ε : ℝ := ((2:ℝ)^n)⁻¹
  have he : 0<ε := by dsimp [ε]; positivity
  have hB : 0<B := by linarith [hcircle.1]
  have hκ0 : 0<κ := hB.trans_le hκ
  have hcut : 0<κ*ε := mul_pos hκ0 he
  have hBe : B*ε≤stop := (mul_le_mul_of_nonneg_right hκ he.le).trans hκstop
  let p := profile ε he B stop
  have hp : ∀ t,0<p t := profile_pos hcircle ε he stop hBe hstop
  have hc := hcircle.2.2.2.1
  have hQ := hcircle.2.2.1
  have hC₄ := hcircle.2.1
  have hC₃ : 0≤C₃ := hc.le.trans hcC₃
  have hKB : 1≤C₄*Q := one_le_mul_of_one_le_of_one_le hC₄ hQ
  have hKH : 1≤C₃*Q/c := by
    apply (le_div_iff₀ hc).mpr
    have hh : C₃≤C₃*Q := le_mul_of_one_le_right hC₃ hQ
    simpa only [one_mul] using hcC₃.trans hh
  apply envelope_geometryBound
  · intro h
    exact hf _
  intro S hS u hu
  let G := T.geometry hplane n z (selectedSlot slot S) (fun i => hdisp i.val)
  let R := OptimizedForestStop.radius stop D S.card
  have hRstop : R≤stop := OptimizedForestStop.radius_le_stop stop D S.card
  have hcutR : κ*ε≤R := hcutRadius S hS
  let sites := testSupport hplane T n ∪ probeSites G (κ*ε) R hcut
  let exterior := UnitReferenceCover.slot false sites
  have hext : ∀ v∈testSupport hplane T n,∃ ie,exterior ie=v := by
    intro v hv
    exact UnitReferenceCover.slot_covers false sites v (Finset.mem_union_left _ hv)
  have hsites : ∀ v∈sites,∃ ie,exterior ie=v := UnitReferenceCover.slot_covers false sites
  have hprobes : ∀ a ha,(dimerLifeProbe G (κ*ε) R hcut a ha).region⊆(sites:Set Site) := by
    intro a ha v hv
    exact Finset.mem_union_right _ (probeSites_covers G (κ*ε) R hcut a ha hv)
  have hspan : ∀ i e f,dist (position ε (exterior (i,e)))
      (position ε (exterior (i,f)))≤G.margin := by
    intro i e f
    exact (unit_cover_span ε he sites i e f).trans G.mesh_le_margin
  have hresolution : B*ε≤8*(κ*ε) := by
    have h := mul_le_mul_of_nonneg_right hκ he.le
    linarith
  exact selected_base_forest_bound hplane hbulk hhalf T n hn z slot exterior hdisp S
    hspan hcover hext (κ*ε) R hcut hcutR (hRstop.trans hfeature) (hsmall S)
    u outer hu hf (alpha ε he B stop) (normalized p R)
    (alpha_fourArm_at_mesh hcircle ε he stop hstop) hthree sites hsites hprobes hresolution
    hcircle.2.2.2.2.1.le hcircle.2.2.2.2.2.1.le hc hC₃ (by linarith)
    (le_max_left _ _) hKB hKH
    (fun t => (normalized_pos p (hp t) (hp R)).ne')
    (normalized_at_stop p (hp R).ne')
    (fun t _ _ => normalized_pos p (hp t) (hp R))
    (by
      intro a b ha hab hb
      rw [normalized_ratio p (hp R).ne']
      exact profile_quasi hcircle ε he stop hBe hstop a b ha hab (hb.trans hRstop))
    (fun a b ha hab hb => normalized_lower p (hp R)
      (profile_growth hcircle ε he stop hBe hstop a b ha hab (hb.trans hRstop)))
    (fun a b hba ha hab hb => alpha_lower hcircle ε he stop hstop a b hba ha hab (hb.trans hRstop))

#print axioms circular_envelope_geometryBound
end
end ExceptionalTimes.CircularForestGeometry
