import ExceptionalTimes.Model
import Mathlib.Tactic.Linarith

/-! Integer choices for uniformly wide inner and outer collars. -/

namespace ExceptionalTimes.WideCollarRadii

def outerStart (K R : ℕ) : ℕ := R/(16*K)

theorem chosen_radii {K r R : ℕ} (hK : 2 ≤ K) (hr : 2 ≤ r)
    (hR : 32*K*r ≤ R) :
    let v := outerStart K R
    2*r ≤ v ∧
    r ≤ 2*r ∧ 2*r ≤ 2*K*r ∧ 2*K*r+1 ≤ 2*K*v ∧
    r ≤ v ∧ v ≤ K*v ∧ K*v+1 ≤ 2*K*v ∧
    2*K*v ≤ R ∧ 2*K*v ≤ R/2 ∧ R+1 < 64*K*v := by
  dsimp only
  let v := outerStart K R
  have hden : 0 < 16*K := by omega
  have hrv : 2*r ≤ v := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    nlinarith
  have hvpos : 0 < v := by omega
  have hlow : 16*K*v ≤ R := by
    simpa only [v,outerStart,Nat.mul_comm] using Nat.div_mul_le_self R (16*K)
  have hupp : R < 16*K*(v+1) := by
    simpa only [v,outerStart] using Nat.lt_mul_div_succ R hden
  have hKv : v ≤ K*v := Nat.le_mul_of_pos_left v (by omega)
  have hKr : r ≤ K*r := Nat.le_mul_of_pos_left r (by omega)
  have hpos : 0 < K*v := Nat.mul_pos (by omega) hvpos
  have ht : 2*K*v ≤ R/2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    nlinarith
  refine ⟨hrv,by omega,by nlinarith,by nlinarith,by omega,hKv,by nlinarith,
    by nlinarith,ht,?_⟩
  nlinarith

#print axioms chosen_radii

end ExceptionalTimes.WideCollarRadii
