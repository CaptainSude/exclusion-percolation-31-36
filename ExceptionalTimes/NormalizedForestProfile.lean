import ExceptionalTimes.CanonicalForestNumeric
import ExceptionalTimes.ForestArmRadial

/-! Changing the forest stop only renormalizes a static arm profile.
The resulting edge product is the literal weighted radial product used
by the lattice integration theorem. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.NormalizedForestProfile

open PairSquareSewing ForestArmRadial ForestGeometry ForestLifeGeometry RootKruskal

noncomputable def normalized (p : ℝ → ℝ) (stop t : ℝ) : ℝ := p t/p stop

theorem normalized_at_stop (p : ℝ → ℝ) {stop : ℝ} (h : p stop≠0) :
    normalized p stop stop=1 := div_self h

theorem normalized_pos (p : ℝ → ℝ) {stop t : ℝ} (ht : 0<p t) (hs : 0<p stop) :
    0<normalized p stop t := div_pos ht hs

theorem normalized_ratio (p : ℝ → ℝ) {stop a b : ℝ} (hs : p stop≠0) :
    normalized p stop a/normalized p stop b=p a/p b := by
  unfold normalized
  exact div_div_div_cancel_right₀ hs (p a) (p b)

theorem normalized_lower (p : ℝ → ℝ) {stop a b C g : ℝ} (hs : 0<p stop)
    (h : p b≤C*(b/a)^g*p a) :
    normalized p stop b≤C*(b/a)^g*normalized p stop a := by
  have hh := div_le_div_of_nonneg_right h hs.le
  dsimp only [normalized]
  convert hh using 1
  ring

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable local instance : DecidableEq (I ⊕ J) := Classical.decEq _

theorem forestValue_radial_bound (G : DimerGeometry I J)
    {cutoff stop C K g : ℝ} (hcut : 0<cutoff) (hcutstop : cutoff≤stop)
    (p : ℝ → ℝ) (hpstop : p stop=1)
    (hp : ∀ t,0<t → t≤stop → 0<p t)
    (hlower : ∀ a b,0<a → a≤b → b≤stop → p b≤C*(b/a)^g*p a) :
    canonicalForestValue G cutoff stop C K g p≤
      ((K*C^2*256^g)^2*Real.exp (g*(1+4*G.margin/cutoff)))^Fintype.card I*
        p cutoff^Fintype.card I*
        (C*stop^g)^((recorded selectedRoot (dimerAnchor G) cutoff ⊓
          threshold (dimerAnchor G) cutoff stop).edgeFinset.card)*
        ∏ e∈(recorded selectedRoot (dimerAnchor G) cutoff ⊓
          threshold (dimerAnchor G) cutoff stop).edgeFinset,
          radialEdge (dimerAnchor G) cutoff g stop e := by
  have h := profile_edge_product_le selectedRoot (dimerAnchor G) hcut p hpstop hp hlower
  let A := ((K*C^2*256^g)^2*Real.exp (g*(1+4*G.margin/cutoff)))^Fintype.card I
  have hA : 0≤A := by dsimp [A]; positivity
  have hh := mul_le_mul_of_nonneg_left h (mul_nonneg hA (pow_nonneg (hp cutoff hcut hcutstop).le (Fintype.card I)))
  simp only [one_div,Finset.prod_inv_distrib] at hh
  convert hh using 1
  · dsimp [canonicalForestValue,A]
    ring
  · dsimp [A]
    ring

theorem normalized_cutoff_le (p : ℝ → ℝ) {cutoff R stop C g : ℝ}
    (hR : 0<R) (hRs : R≤stop) (hpc : 0≤p cutoff) (hpR : 0<p R)
    (hpstop : p stop=1)
    (hlower : ∀ a b,0<a → a≤b → b≤stop → p b≤C*(b/a)^g*p a) :
    normalized p R cutoff≤(C*stop^g)*p cutoff*R^(-g) := by
  have h := mul_le_mul_of_nonneg_left
    (inverse_profile_le p hR hRs hpR hpstop hlower) hpc
  convert h using 1
  · dsimp [normalized]
    ring
  · ring

theorem forestValue_normalized_bound (G : DimerGeometry I J)
    {cutoff R stop C K g : ℝ} (hcut : 0<cutoff) (hcutR : cutoff≤R)
    (hRs : R≤stop) (hC : 0≤C) (p : ℝ → ℝ) (hpstop : p stop=1)
    (hp : ∀ t,0<t → t≤stop → 0<p t)
    (hlower : ∀ a b,0<a → a≤b → b≤stop → p b≤C*(b/a)^g*p a) :
    canonicalForestValue G cutoff R C K g (normalized p R)≤
      (((K*C^2*256^g)^2*Real.exp (g*(1+4*G.margin/cutoff)))*(C*stop^g))^Fintype.card I*
        p cutoff^Fintype.card I*R^(-g*(Fintype.card I:ℝ))*
        (C*R^g)^((recorded selectedRoot (dimerAnchor G) cutoff ⊓
          threshold (dimerAnchor G) cutoff R).edgeFinset.card)*
        ∏ e∈(recorded selectedRoot (dimerAnchor G) cutoff ⊓
          threshold (dimerAnchor G) cutoff R).edgeFinset,
          radialEdge (dimerAnchor G) cutoff g R e := by
  have hR : 0<R := hcut.trans_le hcutR
  have hpR := hp R hR hRs
  have hpc := hp cutoff hcut (hcutR.trans hRs)
  have hlocal := forestValue_radial_bound G (K := K) hcut hcutR (normalized p R)
    (normalized_at_stop p hpR.ne')
    (fun t ht htR => normalized_pos p (hp t ht (htR.trans hRs)) hpR)
    (fun a b ha hab hbR => normalized_lower p hpR (hlower a b ha hab (hbR.trans hRs)))
  have hnorm := pow_le_pow_left₀ (div_nonneg hpc.le hpR.le)
    (normalized_cutoff_le p hR hRs hpc.le hpR hpstop hlower) (Fintype.card I)
  apply hlocal.trans
  have h1 := mul_le_mul_of_nonneg_left hnorm
    (by positivity : 0≤((K*C^2*256^g)^2*Real.exp (g*(1+4*G.margin/cutoff)))^Fintype.card I)
  have h2 := mul_le_mul_of_nonneg_right h1
    (pow_nonneg (mul_nonneg hC (Real.rpow_nonneg hR.le g))
      (recorded selectedRoot (dimerAnchor G) cutoff ⊓ threshold (dimerAnchor G) cutoff R).edgeFinset.card)
  have h3 := mul_le_mul_of_nonneg_right h2
    (Finset.prod_nonneg (s := (recorded selectedRoot (dimerAnchor G) cutoff ⊓
      threshold (dimerAnchor G) cutoff R).edgeFinset)
      (fun e _ => radialEdge_nonneg (dimerAnchor G) cutoff g R e))
  convert h3 using 1 <;> simp only [normalized,Real.rpow_mul_natCast hR.le,mul_pow]
  all_goals ring

#print axioms forestValue_normalized_bound
#print axioms forestValue_radial_bound

end ExceptionalTimes.NormalizedForestProfile


