import ExceptionalTimes.LatticeRadial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The k-dependent stop remains above the microscopic cutoff for every
nonzero coefficient degree, by actual lattice packing. -/

open scoped Classical

namespace ExceptionalTimes.OptimizedForestStop

open LatticeRadial

noncomputable def radius (stop D : ℝ) (k : ℕ) : ℝ :=
  min stop (D/Real.sqrt k)

theorem sqrt_pos {k : ℕ} (hk : 1≤k) : 0<Real.sqrt k :=
  Real.sqrt_pos.mpr (by exact_mod_cast (show 0<k by omega))

theorem sqrt_ge_one {k : ℕ} (hk : 1≤k) : 1≤Real.sqrt k := by
  have h : (1:ℝ)≤k := by exact_mod_cast hk
  simpa using Real.sqrt_le_sqrt h

theorem radius_pos {stop D : ℝ} {k : ℕ} (hstop : 0<stop) (hD : 0<D) (hk : 1≤k) :
    0<radius stop D k := lt_min hstop (div_pos hD (sqrt_pos hk))

theorem radius_le_stop (stop D : ℝ) (k : ℕ) : radius stop D k≤stop := min_le_left _ _

theorem radius_bounds {stop D : ℝ} {k : ℕ} (hstop : 0<stop) (_hD : 0<D) (hk : 1≤k) :
    min stop D / Real.sqrt k≤radius stop D k ∧ radius stop D k≤D/Real.sqrt k := by
  constructor
  · apply le_min
    · apply (div_le_iff₀ (sqrt_pos hk)).mpr
      exact (min_le_left stop D).trans (le_mul_of_one_le_right hstop.le (sqrt_ge_one hk))
    · exact div_le_div_of_nonneg_right (min_le_right stop D) (sqrt_pos hk).le
  · exact min_le_right _ _

theorem inverse_sqrt_eq_rpow (k : ℕ) :
    (Real.sqrt (k:ℝ))⁻¹=(k:ℝ)^(-(1/2:ℝ)) := by
  rw [Real.sqrt_eq_rpow,Real.rpow_neg (Nat.cast_nonneg k)]

theorem radius_rpow_bounds {stop D : ℝ} {k : ℕ} (hstop : 0<stop) (hD : 0<D) (hk : 1≤k) :
    min stop D*(k:ℝ)^(-(1/2:ℝ))≤radius stop D k ∧
      radius stop D k≤D*(k:ℝ)^(-(1/2:ℝ)) := by
  simpa only [div_eq_mul_inv,inverse_sqrt_eq_rpow] using radius_bounds hstop hD hk

/-- k cannot exceed the number of actual anchor sites. The resulting
cutoff inequality therefore holds for every nonzero expansion degree. -/
theorem cutoff_le_radius (s : Finset Site) {ε r₀ κ stop : ℝ} (center : ℂ)
    (hε : 0<ε) (hr₀ : ε≤r₀) (hκ : 0≤κ) (hstop : κ*ε≤stop)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀)
    {k : ℕ} (hk : 1≤k) (hks : k≤s.card) :
    κ*ε≤radius stop (11*κ*r₀) k := by
  have hmass := scaled_ball_mass_le s hε hr₀ center hs
  have hcast : (k:ℝ)≤s.card := by exact_mod_cast hks
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hsq := Real.sq_sqrt hkpos.le
  have hsqrt := sqrt_pos hk
  have hr : 0<r₀ := hε.trans_le hr₀
  have hpacking : ε*Real.sqrt k≤11*r₀ := by
    have hmul := mul_le_mul_of_nonneg_left hcast (sq_nonneg ε)
    nlinarith
  apply le_min hstop
  apply (le_div_iff₀ hsqrt).mpr
  nlinarith [mul_le_mul_of_nonneg_left hpacking hκ]

#print axioms cutoff_le_radius
#print axioms radius_rpow_bounds

end ExceptionalTimes.OptimizedForestStop

