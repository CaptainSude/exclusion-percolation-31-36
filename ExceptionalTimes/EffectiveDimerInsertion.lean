import ExceptionalTimes.DimerExpansion
import ExceptionalTimes.SourcePolygonCalibration
import ExceptionalTimes.ExpansionLimit

/-! A centered effective insertion expresses each actual semigroup
exactly; its difference from the first-order insertion has variation O(t). -/

open scoped Classical BigOperators
namespace ExceptionalTimes.EffectiveDimerInsertion
noncomputable section
open DimerLaw DimerExpansion CenteredBlocks BlockExpansion ExpansionLimit PairSquareSewing

def insertion : Rule→History→ℝ
  | .canonical => canonicalInsertion
  | .refresh => refreshInsertion

def law : Rule→ℝ→History→ℝ
  | .canonical => canonicalLaw
  | .refresh => refreshLaw

def remainder : Rule→ℝ→History→ℝ
  | .canonical => canonicalRemainder
  | .refresh => refreshRemainder

def correction (rule : Rule) (t : ℝ) (h : History) : ℝ :=
  t⁻¹*remainder rule t h

def effective (rule : Rule) (t : ℝ) (h : History) : ℝ :=
  insertion rule h+correction rule t h

theorem insertion_centered (rule : Rule) : ∑ h,insertion rule h=0 := by
  cases rule
  · exact canonicalInsertion_centered
  · exact refreshInsertion_centered

theorem insertion_variation (rule : Rule) : variation (insertion rule)≤1 := by
  cases rule
  · change variation canonicalInsertion≤1
    rw [canonicalInsertion_variation]
    norm_num
  · exact refreshInsertion_variation.le

theorem correction_centered (rule : Rule) (t : ℝ) : ∑ h,correction rule t h=0 := by
  simp only [correction,←Finset.mul_sum]
  have hh : ∑ h,remainder rule t h=0 := by
    cases rule
    · exact canonicalRemainder_centered t
    · exact refreshRemainder_centered t
  rw [hh,mul_zero]

theorem correction_variation (rule : Rule) {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    variation (correction rule t)≤t := by
  have hr : variation (remainder rule t)≤t^2 := by
    cases rule
    · exact (canonicalRemainder_variation ht.le ht1).trans (by nlinarith [sq_nonneg t])
    · exact (refreshRemainder_variation ht.le ht1).trans (by nlinarith [sq_nonneg t])
  unfold correction
  rw [variation_smul,abs_of_pos (inv_pos.mpr ht)]
  calc
    _≤t⁻¹*t^2 := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr ht.le)
    _=t := by field_simp

theorem effective_centered (rule : Rule) (t : ℝ) : ∑ h,effective rule t h=0 := by
  simp only [effective,Finset.sum_add_distrib,insertion_centered,correction_centered,add_zero]

theorem effective_variation (rule : Rule) {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    variation (effective rule t)≤2 :=
  (variation_add _ _).trans ((add_le_add (insertion_variation rule)
    (correction_variation rule ht ht1)).trans (by linarith))

theorem exact_law (rule : Rule) {t : ℝ} (ht : t≠0) (h : History) :
    law rule t h=base h+t*effective rule t h := by
  have he : law rule t h=base h+t*insertion rule h+remainder rule t h := by
    cases rule
    · exact canonicalLaw_linear_remainder t h
    · exact refreshLaw_linear_remainder t h
  rw [he]
  unfold effective correction
  field_simp
  ring

variable {B : Type*} [Fintype B]

theorem coefficient_smul (p u : B→History→ℝ) (f : (B→History)→ℝ) (c : ℝ) (k : ℕ) :
    coefficient p (fun b h => c*u b h) f k=c^k*coefficient p u f k := by
  unfold coefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [selectedKernel_smul,(Finset.mem_filter.mp hS).2]

def scaledCoefficient (rule : Rule) (f : (B→History)→ℝ) (scale : ℝ) (k : ℕ) : ℝ :=
  scale^k*coefficient (fun _ => base) (fun _ => insertion rule) f k

def effectiveCoefficient (rule : Rule) (f : (B→History)→ℝ)
    (scale T : ℝ) (k : ℕ) : ℝ :=
  scale^k*coefficient (fun _ => base) (fun _ => effective rule (T*scale)) f k

theorem actual_series (rule : Rule) (f : (B→History)→ℝ)
    (scale T : ℝ) (ht : T*scale≠0) :
    kernel (fun _ : B => law rule (T*scale)) f=
      ∑' k : ℕ,T^k*effectiveCoefficient rule f scale T k := by
  have he : (fun _ : B => law rule (T*scale))=
      fun _ h => base h+T*(scale*effective rule (T*scale) h) := by
    funext b h
    rw [exact_law rule ht]
    ring
  rw [he,kernel_eq_tsum_coefficients]
  apply tsum_congr
  intro k
  rw [coefficient_smul]
  rfl

#print axioms actual_series
#print axioms correction_variation
end
end ExceptionalTimes.EffectiveDimerInsertion
