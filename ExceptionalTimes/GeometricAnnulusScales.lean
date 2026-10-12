import ExceptionalTimes.CanonicalScaleProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Explicit radii for separated fixed-aspect annuli, and the numerical
conversion of their probability product into a power of the scale ratio. -/

namespace ExceptionalTimes.GeometricAnnulusScales

def scale (M m i : ℕ) : ℕ := (2*M)^i*m

theorem scale_zero (M m : ℕ) : scale M m 0=m := by simp [scale]

theorem scale_succ (M m i : ℕ) : scale M m (i+1)=2*M*scale M m i := by
  simp only [scale,pow_succ]
  ring

theorem scale_mono {M m : ℕ} (hM : 1≤M) : Monotone (scale M m) := by
  intro i j hij
  exact Nat.mul_le_mul_right m (Nat.pow_le_pow_right (by omega) hij)

theorem base_le_scale {M m : ℕ} (hM : 1≤M) (i : ℕ) : m≤scale M m i := by
  simpa only [scale_zero] using scale_mono (m := m) hM (Nat.zero_le i)

theorem gap {M m d i j : ℕ} (hM : 1≤M) (hd : 2*d<m) (hij : i<j) :
    M*scale M m i+2*d<scale M m j := by
  have hi := base_le_scale (m := m) hM i
  have hs := scale_mono (m := m) hM (show i+1≤j by omega)
  rw [scale_succ] at hs
  have hp : scale M m i≤M*scale M m i := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith

theorem outer_le_last {M m N i : ℕ} (hM : 1≤M) (hi : i<N) :
    M*scale M m i≤scale M m N := by
  have h := scale_mono (m := m) hM (show i+1≤N by omega)
  rw [scale_succ] at h
  nlinarith

theorem scale_real (M m i : ℕ) : (scale M m i : ℝ)=(2*(M:ℝ))^i*(m:ℝ) := by
  simp only [scale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]

theorem product_power_le {Λ a q ratio : ℝ} (hΛ : 1<Λ) (ha : 0≤a)
    (hratio : 0<ratio) (N : ℕ) (hupper : ratio≤Λ^(N+1))
    (hq : q≤(Λ^(-a))^N) : q≤Λ^a*ratio^(-a) := by
  have hΛ0 : 0<Λ := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos hratio hupper (neg_nonpos.mpr ha)
  have hm := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hΛ0.le a)
  have he : Λ^a*(Λ^(N+1))^(-a)=(Λ^(-a))^N := by
    rw [pow_succ,Real.mul_rpow (pow_nonneg hΛ0.le _) hΛ0.le,
      ←Real.rpow_pow_comm hΛ0.le]
    rw [Real.rpow_neg hΛ0.le]
    have hnz : Λ^a≠0 := (Real.rpow_pos_of_pos hΛ0 a).ne'
    field_simp
  rw [he] at hm
  exact hq.trans hm

theorem probability_power_le {Λ a q r R : ℝ} (hΛ : 1<Λ) (ha : 0≤a)
    (hr : 0<r) (hR : 0<R) (N : ℕ) (hupper : R/r≤Λ^(N+1))
    (hq : q≤(Λ^(-a))^N) : q≤Λ^a*(r/R)^a := by
  have h := product_power_le hΛ ha (div_pos hR hr) N hupper hq
  simpa only [Real.rpow_neg_eq_inv_rpow,inv_div] using h

theorem exists_annulus_count {Λ r R : ℝ} (hΛ : 1<Λ) (hr : 0<r) (hrR : r≤R) :
    ∃ N : ℕ, Λ^N*r≤R ∧ R<Λ^(N+1)*r := by
  have hratio : 1≤R/r := (le_div_iff₀ hr).mpr (by simpa using hrR)
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near hratio hΛ
  exact ⟨N,(le_div_iff₀ hr).mp hlo,(div_lt_iff₀ hr).mp hhi⟩

#print axioms gap
#print axioms probability_power_le
#print axioms exists_annulus_count

end ExceptionalTimes.GeometricAnnulusScales
