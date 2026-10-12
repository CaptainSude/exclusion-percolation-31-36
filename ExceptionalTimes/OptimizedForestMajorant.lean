import ExceptionalTimes.ForestCounting
import ExceptionalTimes.OptimizedForestStop

/-! The counted, radius-dependent forest integral has a summable
majorant once the actual stop lies between constant multiples of k^(-1/2). -/

open scoped Classical BigOperators

namespace ExceptionalTimes.OptimizedForestMajorant

open ForestCounting

theorem inverse_half_square (k : ℕ) :
    ((k:ℝ)^(-(1/2:ℝ)))^2=(k:ℝ)⁻¹ := by
  rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg k)]
  convert Real.rpow_neg_one (k:ℝ) using 1; norm_num

theorem radius_square_le {k : ℕ} {R D : ℝ} (hR : 0≤R)
    (hbound : R≤D*(k:ℝ)^(-(1/2:ℝ))) : R^2≤D^2/k := by
  calc
    _ ≤ (D*(k:ℝ)^(-(1/2:ℝ)))^2 := pow_le_pow_left₀ hR hbound 2
    _ = _ := by rw [mul_pow,inverse_half_square]; ring

theorem inverse_radius_power {k : ℕ} {R d g : ℝ} (hk : 1≤k)
    (hd : 0<d) (hg : 0≤g) (hlower : d*(k:ℝ)^(-(1/2:ℝ))≤R) :
    R^(-g*(k:ℝ))≤(d^(-g))^k*(k:ℝ)^(g*k/2) := by
  have hk0 : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  calc
    _ ≤ (d*(k:ℝ)^(-(1/2:ℝ)))^(-g*(k:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hd (Real.rpow_pos_of_pos hk0 _)) hlower
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg) hk0.le)
    _ = _ := by
      rw [Real.mul_rpow hd.le (Real.rpow_nonneg hk0.le _),
        ←Real.rpow_mul hk0.le,Real.rpow_mul hd.le,Real.rpow_natCast]
      congr 1
      ring

theorem radius_counted_sum_le (k J : ℕ) (hk : 1≤k)
    {R D A M : ℝ} (hR : 0≤R) (hA : 0≤A) (hM : 0≤M)
    (hupper : R≤D*(k:ℝ)^(-(1/2:ℝ))) :
    (∑ j∈Finset.range (k+1),(((k+J)^2).choose j : ℝ)*(A*R^2)^j*M^(k-j))≤
      (max (A*D^2) M)^k*binomialWeight ((k+J)^2) k (1/(k:ℝ)) := by
  have hk0 : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  let L := max (A*D^2) M
  have hL : 0≤L := hM.trans (le_max_right _ _)
  have hbase : A*R^2≤L*(1/(k:ℝ)) := by
    calc
      _ ≤ A*(D^2/k) := mul_le_mul_of_nonneg_left (radius_square_le hR hupper) hA
      _ ≤ L*(1/(k:ℝ)) := by
        have h := mul_le_mul_of_nonneg_right (le_max_left (A*D^2) M) (one_div_pos.mpr hk0).le
        convert h using 1; ring
  unfold binomialWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j≤k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hterm : (A*R^2)^j*M^(k-j)≤L^k*(1/(k:ℝ))^j := by
    calc
      _ ≤ (L*(1/(k:ℝ)))^j*L^(k-j) := mul_le_mul
        (pow_le_pow_left₀ (mul_nonneg hA (sq_nonneg R)) hbase j)
        (pow_le_pow_left₀ hM (le_max_right _ _) _)
        (pow_nonneg hM _) (pow_nonneg (mul_nonneg hL (one_div_pos.mpr hk0).le) _)
      _ = _ := by
        rw [mul_pow]
        calc
          _ = (L^j*L^(k-j))*(1/(k:ℝ))^j := by ring
          _ = _ := by rw [←pow_add,Nat.add_sub_of_le hjk]
  have h := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg (((k+J)^2).choose j))
  convert h using 1 <;> ring

/-- Explicit constants and exponent: beta=1-g/2. The left side is the
actual binomial forest count after weighted leaf integration and the exact
1/k! insertion multiplicity. -/
theorem counted_majorant (k J : ℕ) (hk : 1≤k)
    {R d D A M g : ℝ} (hR : 0<R) (hd : 0<d) (hA : 0≤A) (hM : 0≤M) (hg : 0≤g)
    (hlower : d*(k:ℝ)^(-(1/2:ℝ))≤R)
    (hupper : R≤D*(k:ℝ)^(-(1/2:ℝ))) :
    R^(-g*(k:ℝ))/(k.factorial:ℝ)*
      (∑ j∈Finset.range (k+1),(((k+J)^2).choose j : ℝ)*(A*R^2)^j*M^(k-j))≤
      (d^(-g)*max (A*D^2) M*(Real.exp 1*Real.exp (((J:ℝ)+1)^2)))^k*
        (k:ℝ)^(-(1-g/2)*k) := by
  let L := max (A*D^2) M
  have hL : 0≤L := hM.trans (le_max_right _ _)
  have hfac : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hbin : 0≤binomialWeight ((k+J)^2) k (1/(k:ℝ)) := by
    unfold binomialWeight
    positivity
  calc
    _ ≤ ((d^(-g))^k*(k:ℝ)^(g*k/2))/(k.factorial:ℝ)*
        (L^k*binomialWeight ((k+J)^2) k (1/(k:ℝ))) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (inverse_radius_power hk hd hg hlower) hfac.le
      · exact radius_counted_sum_le k J hk hR.le hA hM hupper
      · exact Finset.sum_nonneg (fun j _ => by positivity)
      · positivity
    _ = (d^(-g)*L)^k*forestMajorant J (1-g/2) k := by
      unfold forestMajorant
      rw [show (1-(1-g/2))*(k:ℝ)=g*k/2 by ring,mul_pow]
      ring
    _ ≤ (d^(-g)*L)^k*((Real.exp 1*Real.exp (((J:ℝ)+1)^2))^k*
        (k:ℝ)^(-(1-g/2)*k)) :=
      mul_le_mul_of_nonneg_left (forestMajorant_le J k hk (1-g/2))
        (pow_nonneg (mul_nonneg (Real.rpow_nonneg hd.le _) hL) _)
    _ = _ := by rw [mul_pow]; ring

#print axioms counted_majorant

end ExceptionalTimes.OptimizedForestMajorant





