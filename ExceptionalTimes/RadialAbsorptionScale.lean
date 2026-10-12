import ExceptionalTimes.DyadicPacking
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The radial variance coefficient can always be absorbed by a fixed
integer ratio between the macroscopic hole and the mesoscopic cell size.
This is a numerical consequence of a strictly positive power exponent. -/

open Filter
open scoped Topology

namespace ExceptionalTimes.RadialAbsorptionScale

theorem exists_ratio (L : ℕ) (B h : ℝ) (hB : 0≤B) (hh : 0<h) :
    ∃ N : ℕ,L≤N ∧ 1≤N ∧ ∀ m r : ℕ,0<m → N*m≤r →
      B*((m : ℝ)/r)^h≤1/2 := by
  have ht : Tendsto (fun n : ℕ => B*(1/(n : ℝ))^h) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).rpow_const_nhds_zero hh).const_mul B
  obtain ⟨n,hn⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)))
  let N := max L (max 1 n)
  have hLN : L≤N := le_max_left _ _
  have h1N : 1≤N := (le_max_left _ _).trans (le_max_right _ _)
  have hnN : n≤N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨N,hLN,h1N,?_⟩
  intro m r hm hmr
  have hN : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hm' : (0 : ℝ)<m := by exact_mod_cast hm
  have hr : (0 : ℝ)<r := by
    exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos (by omega) hm) hmr)
  have hmr' : (N : ℝ)*m≤r := by exact_mod_cast hmr
  have hratio : (m : ℝ)/r≤1/(N : ℝ) := by
    apply (div_le_div_iff₀ hr hN).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hm'.le hr.le) hratio hh.le) hB).trans (hn N hnN).le

theorem exists_radial_ratio (L : ℕ) (C δ h : ℝ) (hC : 0≤C) (hδ : 0<δ) (hh : 0<h) :
    ∃ N : ℕ,L≤N ∧ 1≤N ∧ ∀ m r : ℕ,0<m → N*m≤r →
      98*(C/δ^6)*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h≤1/2 := by
  apply exists_ratio L _ h _ hh
  exact mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hC (pow_nonneg hδ.le 6)))
    (DyadicPacking.dyadicConstant_pos (by linarith)).le

#print axioms exists_ratio
#print axioms exists_radial_ratio

end ExceptionalTimes.RadialAbsorptionScale
