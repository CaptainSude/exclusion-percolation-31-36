import ExceptionalTimes.ForestGeometryEnvelope

/-! A single all-degree bound for the actual per-selection geometry.
The optimized radius stays above the microscopic cutoff by proved lattice
packing, including the largest nonzero degrees. No tail estimate is assumed. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.ForestDegreeMass
open PairSquareSewing ForestGeometryEnvelope ForestSelectionIntegral CanonicalForestOrdered
open NormalizedForestProfile SelectedPerturbation InsertionCounting LatticeRadial
open ForestCoefficientIntegral OptimizedForestStop

variable {B J : Type*} [Fintype B] [Fintype J]

theorem all_degree_bound (s : Finset Site) (anchor : B ↪ s)
    (G : (S : Finset B) → DimerGeometry S J)
    {ε κ g stop r C K P L S₀ : ℝ} (center : ℂ)
    (hε : 0<ε) (hκ : 0<κ) (hg : 0≤g) (hg2 : g<2)
    (hcut : κ*ε≤stop) (hr : ε≤r) (hC : 0≤C) (hP : 0≤P) (hL : 0≤L) (hS : 0<S₀)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) (root : J → ℂ)
    (hroot : ∀ S,(G S).root=root)
    (hanchor : ∀ (S : Finset B) (i : S),position (G S).mesh ((G S).endpoint (i,0))=
      scaledEmbedding ε (anchor i.val))
    (hPbound : ∀ S,prefactor (G S) (κ*ε) stop C K g≤P)
    (p : ℝ→ℝ) (hp : ∀ t,0<p t) (hpstop : p stop=1)
    (hlower : ∀ a t,0<a → a≤t → t≤stop → p t≤C*(t/a)^g*p a)
    (hcal : p (κ*ε)≤L*S₀) (k : ℕ) :
    (ε^2/S₀)^k*geometryDegree (envelope G (κ*ε) stop (11*κ*r) C K g p) k≤
      (P*L*summationConstant (Fintype.card J) (min stop (11*κ*r)) (11*κ*r) C κ g r)^k*
        (k:ℝ)^(-(1-g/2)*k) := by
  by_cases hk0 : k=0
  · subst k
    rw [geometryDegree_zero,envelope_empty]
    simp
  have hk : 1≤k := by omega
  by_cases hkB : Fintype.card B<k
  · rw [geometryDegree_gt_card _ hkB,mul_zero]
    have hstop0 : 0≤stop := (mul_nonneg hκ.le hε.le).trans hcut
    have hD0 : 0≤11*κ*r := mul_nonneg (mul_nonneg (by norm_num) hκ.le) (hε.le.trans hr)
    exact mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg hP hL)
      (summationConstant_nonneg _ (le_min hstop0 hD0))) _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hBk : k≤Fintype.card B := by omega
  have hBs : Fintype.card B≤s.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective anchor anchor.injective
  have hstop : 0<stop := (mul_pos hκ hε).trans_le hcut
  have hr0 : 0<r := hε.trans_le hr
  have hD : 0<11*κ*r := by positivity
  have hR := radius_pos hstop hD hk
  have hcutR := cutoff_le_radius s center hε hr hκ.le hcut hs hk (hBk.trans hBs)
  have hRb := radius_rpow_bounds hstop hD hk
  have hm := selected_forest_integral k hk s anchor G center hε hκ le_rfl hg hg2
    hcutR (radius_le_stop stop (11*κ*r) k) hr hC (lt_min hstop hD) hP
    hRb.1 hRb.2 hs root hroot hanchor hPbound p hpstop (fun t _ _ => hp t) hlower
  rw [envelope_degree G (κ*ε) stop (11*κ*r) C K g p hk]
  let M := summationConstant (Fintype.card J) (min stop (11*κ*r)) (11*κ*r) C κ g r
  have hM : 0≤M := summationConstant_nonneg _ (le_min hstop.le hD.le)
  have hpow : (P*p (κ*ε))^k≤(P*L*S₀)^k := by
    apply pow_le_pow_left₀ (mul_nonneg hP (hp _).le)
    nlinarith [mul_le_mul_of_nonneg_left hcal hP]
  have hm' := hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hpow (pow_nonneg hM k))
    (Real.rpow_nonneg (Nat.cast_nonneg k) (-(1-g/2)*k)))
  calc
    _ = (ε^(2*k)*(∑ S : Selections B k,canonicalForestValue (G S.val) (κ*ε)
        (radius stop (11*κ*r) k) C K g (normalized p (radius stop (11*κ*r) k))))/S₀^k := by
      rw [div_pow,←pow_mul]
      ring
    _ ≤ ((P*L*S₀)^k*M^k*(k:ℝ)^(-(1-g/2)*k))/S₀^k :=
      div_le_div_of_nonneg_right hm' (pow_nonneg hS.le k)
    _ = _ := by
      dsimp only [M]
      simp only [mul_pow]
      field_simp [hS.ne']

#print axioms all_degree_bound
end ExceptionalTimes.ForestDegreeMass
