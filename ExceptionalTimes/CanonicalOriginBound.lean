import ExceptionalTimes.CanonicalOriginAnnulus

/-! The annular decorrelation bound implies a relative bound for the
actual origin one-arm event. Both radius regimes and the precise static
normalization are handled; no independence is supplied as an assumption. -/

open scoped Classical

namespace ExceptionalTimes.CanonicalOriginBound

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar ActivePartitionLaw
open CanonicalRadialLaw CanonicalOriginAnnulus HoleFilling ConcreteCanonicalDriver

variable {B : Type*} [Fintype B]

private theorem small_bound {q α a A C : ℝ} (hα : 0<α) (ha : 0≤a)
    (hC : 0≤C) (hsmall : α≤A*a) (hq : q≤a) :
    q≤(A+C*A^2)*a^2/α := by
  apply hq.trans
  apply (le_div_iff₀ hα).mpr
  have hprod := mul_le_mul_of_nonneg_right hsmall ha
  have hpos : 0≤C*A^2*a^2 := by positivity
  nlinarith only [hprod,hpos]

private theorem large_bound {q α a b A C : ℝ} (hα : 0<α) (ha : 0≤a)
    (hb : 0≤b) (hA : 0≤A) (hC : 0≤C) (hstatic : α*b≤A*a)
    (hq : q≤α*(C*b^2)) : q≤(A+C*A^2)*a^2/α := by
  have hsquare : (α*b)^2≤(A*a)^2 :=
    (sq_le_sq₀ (mul_nonneg hα.le hb) (mul_nonneg hA ha)).mpr hstatic
  have hm := mul_le_mul_of_nonneg_left hsquare hC
  apply (le_div_iff₀ hα).mpr
  have hh := mul_le_mul_of_nonneg_right hq hα.le
  have hpos : 0≤A*a^2 := mul_nonneg hA (sq_nonneg a)
  nlinarith only [hm,hh,hpos]

theorem origin_relative_bound (slot : B×Fin 2 ↪ Site) (z : Site)
    {d s R M : ℕ} (hz : z∈latticeBox d) (hds : d+1≤s) (hM : 2≤M)
    (hp : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (hcover : ∀ v∈latticeBox (R+1),∃ b,slot b=v)
    (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    {A C : ℝ} (hA : 0≤A) (hC : 0≤C)
    (hα : 0<(finiteFairOneArm s).toReal)
    (hsmall : R≤M*s → (finiteFairOneArm s).toReal≤A*(finiteFairOneArm R).toReal)
    (hstatic : M*s<R →
      (finiteFairOneArm s).toReal*
        average (fun x => indicator (WiredArm (pairDecode slot x) (2*s) R)) ≤
          A*(finiteFairOneArm R).toReal)
    (hannulus : M*s<R →
      manyProbability p (fun x => WiredArm (pairDecode slot x) (2*s) R) ≤
        C*(average (fun x => indicator (WiredArm (pairDecode slot x) (2*s) R)))^2) :
    manyProbability p (fun x => OneArm (pairDecode slot x) (0,0) R) ≤
      (A+C*A^2)*(finiteFairOneArm R).toReal^2/(finiteFairOneArm s).toReal := by
  by_cases hR : R≤M*s
  · have hq := many_le_marginal p hp0 hp1 (fun x => OneArm (pairDecode slot x) (0,0) R)
    rw [mean_oneArm_eq_finiteFair slot R hcover] at hq
    exact small_bound hα ENNReal.toReal_nonneg hC (hsmall hR) hq
  · have hlarge : M*s<R := by omega
    have hMs : 2*s≤M*s := Nat.mul_le_mul_right s hM
    have hsR : s≤R := by omega
    have h2sR : 2*s≤R := by omega
    have hq := oneArm_inner_outer_product slot z hz hp (by omega : s+1+d≤2*s)
      h2sR p hp0 hp1
    rw [mean_oneArm_eq_finiteFair slot s (fun v hv =>
      hcover v (latticeBox_mono (by omega) hv))] at hq
    let b := average (fun x => indicator (WiredArm (pairDecode slot x) (2*s) R))
    have hb : 0≤b := average_nonneg (fun _ => indicator_nonneg _)
    have hq' := hq.trans (mul_le_mul_of_nonneg_left (hannulus hlarge) hα.le)
    exact large_bound hα ENNReal.toReal_nonneg hb hA hC (hstatic hlarge) hq'

#print axioms origin_relative_bound

end ExceptionalTimes.CanonicalOriginBound
