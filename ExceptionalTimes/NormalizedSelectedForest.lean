import ExceptionalTimes.WordForestGeometry

/-! Pointwise domination of each actual normalized selected insertion by
the common finite family of ordered forests. This is the bound before
summing over good and bad anchor tuples. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.NormalizedSelectedForest
noncomputable section
open PairSquareSewing DimerExpansion CenteredBlocks BlockExpansion
open SelectedPerturbation InsertionCounting ForestGeometryEnvelope
open ForestSelectionIntegral CanonicalForestOrdered NormalizedForestProfile
open RootedAnchorLabels ForestLatticeFamily ForestIntegration LatticeRadial

variable {A J : Type*} [Fintype A] [Fintype J]

theorem selected_ordered_bound (s : Finset Site) (anchor : A ↪ s)
    (G : (S : Finset A)→DimerGeometry S J) (f : (A→History)→ℝ)
    {ε b stop D C K g P L S₀ : ℝ} (p : ℝ→ℝ)
    (hG : GeometryBound (fun _ => ActualProductTransfer.baseLaw) f
      (envelope G b stop D C K g p))
    (hb : 0<b) (hC : 0≤C) (hP : 0≤P) (hS₀ : 0<S₀)
    (root : J→ℂ) (hroot : ∀ S,(G S).root=root)
    (hanchor : ∀ (S : Finset A) (i : S),position (G S).mesh ((G S).endpoint (i,0))=
      scaledEmbedding ε (anchor i.val))
    (hPbound : ∀ S,prefactor (G S) b stop C K g≤P)
    (hp : ∀ t,0<p t) (hpstop : p stop=1)
    (hlower : ∀ a t,0<a → a≤t → t≤stop → p t≤C*(t/a)^g*p a)
    (hcal : p b≤L*S₀)
    {k : ℕ} (hk : 1≤k) (hcutR : b≤OptimizedForestStop.radius stop D k)
    (o : OrderedSelections A k) (u : A→History→ℝ)
    (hu : ∀ i,∑ h,u i h=0) (huv : ∀ i,variation (u i)≤1) :
    |selectedKernel (fun _ => base) u o.1.val f|/S₀^k≤
      (P*L)^k*(OptimizedForestStop.radius stop D k)^(-g*(k:ℝ))*
        forestTuple k s ε b g (OptimizedForestStop.radius stop D k) C root
          (fun i => anchor (anchorTuple o i)) := by
  let R := OptimizedForestStop.radius stop D k
  have hRs : R≤stop := OptimizedForestStop.radius_le_stop stop D k
  have hR : 0<R := hb.trans_le hcutR
  have hstop : 0<stop := hR.trans_le hRs
  have ho : o.1.val≠∅ := by
    intro he
    have hh := o.1.property
    rw [he,Finset.card_empty] at hh
    omega
  have hv : (∏i∈o.1.val,variation (u i))≤1 :=
    Finset.prod_le_one₀ (fun _ _ => by unfold variation; positivity) (fun i _ => huv i)
  have hsel := hG o.1.val u hu
  have hnonneg := envelope_nonneg G b stop D C K g p hp o.1.val
  have hsel' := hsel.trans (mul_le_of_le_one_right hnonneg hv)
  have hw : ActualProductTransfer.baseLaw.weight=base := rfl
  simp only [hw,envelope,ite_eq_right ho,o.1.property] at hsel'
  have ha := actual_forest_ordered_bound o.2 (G o.1.val) (K := K) hb hcutR hRs hC p hpstop
    (fun t _ _ => hp t) hlower
  rw [hroot o.1.val] at ha
  have hpos : (fun i => position (G o.1.val).mesh ((G o.1.val).endpoint (o.2 i,0)))=
      fun i => scaledEmbedding ε (anchor (anchorTuple o i)) := by
    funext i
    exact hanchor o.1.val (o.2 i)
  rw [hpos] at ha
  change canonicalForestValue (G o.1.val) b R C K g (normalized p R)≤
    prefactor (G o.1.val) b stop C K g^k*p b^k*R^(-g*(k:ℝ))*
      forestTuple k s ε b g R C root (fun i => anchor (anchorTuple o i)) at ha
  have htuple := forestTuple_nonneg k s ε b g R C root
    (fun i => anchor (anchorTuple o i)) hC hR.le
  have hprod : prefactor (G o.1.val) b stop C K g*p b≤P*L*S₀ := by
    calc
      _≤P*p b := mul_le_mul_of_nonneg_right (hPbound _) (hp b).le
      _≤P*(L*S₀) := mul_le_mul_of_nonneg_left hcal hP
      _=_ := by ring
  have hpow := pow_le_pow_left₀
    (mul_nonneg (prefactor_nonneg (G o.1.val) hC hstop.le) (hp b).le) hprod k
  rw [mul_pow] at hpow
  have hupper := ha.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hR.le _)) htuple)
  have hd := div_le_div_of_nonneg_right (hsel'.trans hupper) (pow_nonneg hS₀.le k)
  calc
    _≤((P*L*S₀)^k*R^(-g*(k:ℝ))*
      forestTuple k s ε b g R C root (fun i => anchor (anchorTuple o i)))/S₀^k := hd
    _=_ := by rw [mul_pow]; dsimp [R]; field_simp [hS₀.ne']

#print axioms selected_ordered_bound
end
end ExceptionalTimes.NormalizedSelectedForest
