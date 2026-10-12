import ExceptionalTimes.LocalClockControl

/-! The proved clock-control input forces the actual local pair times
to vanish. This supplies the small-time semigroup expansion threshold. -/

open Filter
open scoped Topology
namespace ExceptionalTimes.ClockVanishing
open AnnulusTransferMixing LocalDimerCalibration IndependentAnnulusInput

theorem reciprocal_tendsto_zero (J : ℕ→ℝ) (h : NewClockControl J) :
    Tendsto (fun n => 1/(2*J n)) atTop (𝓝 0) := by
  obtain ⟨N,hpos,hpow⟩ := h
  obtain ⟨C,_hC,hbound⟩ := hpow (3/8) (by norm_num) (by norm_num)
  have hp : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim : Tendsto (fun n : ℕ => C*((2^n:ℕ):ℝ)^(-(3/8:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero,Nat.cast_pow,Nat.cast_ofNat] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/8)).comp hp).const_mul C
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop N] with n hn
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (hpos n hn).le)
  · filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [show (3/4:ℝ)-3/8=3/8 by norm_num] using hbound n hn

theorem local_scale_tendsto_zero (rule : PairSquareSewing.Rule)
    (h : NewClockControl (localClock rule)) :
    Tendsto (fun n => (mesh n)^2/localS rule n) atTop (𝓝 0) := by
  have he (n : ℕ) : 1/(2*localClock rule n)=(mesh n)^2/localS rule n := by
    simpa only [one_mul] using local_clock_time rule n 1
  simpa only [he] using reciprocal_tendsto_zero _ h

#print axioms local_scale_tendsto_zero
end ExceptionalTimes.ClockVanishing
