import ExceptionalTimes.ForestDiameterLoss

/-! The local scalar arm-enlargement calculation. The logarithmic integral is
literal; static arm inputs enter only as one-scale power and ratio bounds. -/

open scoped BigOperators Classical
open MeasureTheory Set

namespace ExceptionalTimes.ArmEnlargement

open ForestDiameterLoss

noncomputable def clippedRadius (u v size : ℝ) : ℝ := min (max u size) v

theorem le_clippedRadius {u v size : ℝ} (huv : u ≤ v) : u ≤ clippedRadius u v size :=
  le_min (le_max_left _ _) huv

theorem clippedRadius_le (u v size : ℝ) : clippedRadius u v size ≤ v := min_le_right _ _

/-- The integral exactly measures the logarithmic increase of the inner
radius, capped when the annulus becomes empty. -/
theorem logarithmicLoss_eq_log {u v size : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    logarithmicLoss u v size = Real.log (clippedRadius u v size / u) := by
  let r := clippedRadius u v size
  have hur : u ≤ r := le_clippedRadius huv
  have hrv : r ≤ v := clippedRadius_le u v size
  have heq : logarithmicLoss u v size = ∫ t in u..v, ({t : ℝ | t ≤ r}).indicator (fun t => 1/t) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne size] with t hne
    intro ht
    rw [uIoc_of_le huv] at ht
    have hiff : t < size ↔ t ≤ r := by
      constructor
      · intro hts
        exact le_min (hts.le.trans (le_max_right _ _)) ht.2
      · intro htr
        have htm : t ≤ max u size := htr.trans (min_le_left _ _)
        by_cases hsu : size ≤ u
        · rw [max_eq_left hsu] at htm
          exact False.elim ((not_lt_of_ge htm) ht.1)
        · rw [max_eq_right (le_of_not_ge hsu)] at htm
          exact lt_of_le_of_ne htm hne
    change (if t < size then 1/t else 0) = (if t ≤ r then 1/t else 0)
    simp only [hiff]
  rw [heq, intervalIntegral.integral_indicator ⟨hur, hrv⟩,
    integral_one_div_of_pos hu (hu.trans_le hur)]

theorem exponentialLoss_eq_rpow {u v size g : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.exp (g * logarithmicLoss u v size) = (clippedRadius u v size / u)^g := by
  rw [logarithmicLoss_eq_log hu huv, Real.rpow_def_of_pos
    (div_pos (hu.trans_le (le_clippedRadius huv)) hu), mul_comm]

/-- A static lower-power estimate transfers the un-enlarged p-ratio to the
capped enlarged ratio. No probability estimate for a forest is assumed. -/
theorem enlarged_ratio_le (p : ℝ → ℝ) {C g stop u v size : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ stop) (hpv : 0 < p v)
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    p (clippedRadius u v size) / p v ≤
      C * Real.exp (g * logarithmicLoss u v size) * (p u / p v) := by
  have h := hlower u (clippedRadius u v size) hu (le_clippedRadius huv)
    ((clippedRadius_le u v size).trans hv)
  have hd := div_le_div_of_nonneg_right h hpv.le
  rw [exponentialLoss_eq_rpow hu huv]
  convert hd using 1
  ring

/-- The convention for empty annuli is explicit. -/
noncomputable def armCost (α : ℝ → ℝ → ℝ) (inner outer : ℝ) : ℝ :=
  if inner < outer then α inner outer else 1

theorem capped_armCost_le_ratio (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    {Q stop u v size : ℝ} (hu : 0 < u) (hv : v ≤ stop)
    (hQ : 1 ≤ Q) (hpv : 0 < p v)
    (hquasi : ∀ a b, 0 < a → a < b → b ≤ stop → α a b ≤ Q * (p a / p b)) :
    armCost α (max u size) v ≤ Q * (p (clippedRadius u v size) / p v) := by
  by_cases h : max u size < v
  · rw [armCost, ite_eq_left h, clippedRadius, min_eq_left h.le]
    exact hquasi (max u size) v (hu.trans_le (le_max_left _ _)) h hv
  · rw [armCost, ite_eq_right h, clippedRadius, min_eq_right (le_of_not_gt h),
      div_self (ne_of_gt hpv), mul_one]
    exact hQ

/-- One local static ratio estimate and one lower-power estimate pay for the
entire capped enlargement, including a probe that has become empty. -/
theorem enlarged_armCost_le (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    {C Q g stop u v size : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ stop)
    (hQ : 1 ≤ Q) (hpv : 0 < p v)
    (hquasi : ∀ a b, 0 < a → a < b → b ≤ stop → α a b ≤ Q * (p a / p b))
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    armCost α (max u size) v ≤
      (Q*C) * Real.exp (g * logarithmicLoss u v size) * (p u / p v) := by
  apply (capped_armCost_le_ratio α p hu hv hQ hpv hquasi).trans
  have h := mul_le_mul_of_nonneg_left (enlarged_ratio_le p (size := size) hu huv hv hpv hlower)
    ((by norm_num : (0:ℝ) ≤ 1).trans hQ)
  convert h using 1
  ring

theorem ratio_compare (p : ℝ → ℝ) {C g stop u a b v : ℝ}
    (hu : 0 < u) (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v) (hv : v ≤ stop)
    (hC : 0 ≤ C) (hpu : 0 ≤ p u) (hpb : 0 < p b) (hpv : 0 < p v)
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    p a / p b ≤ C^2 * ((a/u)*(v/b))^g * p u / p v := by
  have hb := hu.trans_le (hua.trans hab)
  have haBound := hlower u a hu hua (hab.trans (hbv.trans hv))
  have hbBound := hlower b v hb hbv hv
  apply (div_le_div_iff₀ hpb hpv).mpr
  rw [Real.mul_rpow (div_nonneg (hu.trans_le hua).le hu.le)
    (div_nonneg (hb.trans_le hbv).le hb.le)]
  calc
    p a * p v ≤ (C*(a/u)^g*p u)*p v := mul_le_mul_of_nonneg_right haBound hpv.le
    _ ≤ (C*(a/u)^g*p u)*(C*(v/b)^g*p b) :=
      mul_le_mul_of_nonneg_left hbBound (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg (div_nonneg (hu.trans_le hua).le hu.le) _)) hpu)
    _ = _ := by ring

/-- The exact separation condition required by the geometric probe. -/
noncomputable def separatedArmCost (α : ℝ → ℝ → ℝ) (inner outer : ℝ) : ℝ :=
  if 4 * inner < outer then α inner outer else 1

theorem separatedArmCost_nonneg (α : ℝ → ℝ → ℝ) (hα : ∀ a b, 0 ≤ α a b)
    (inner outer : ℝ) : 0 ≤ separatedArmCost α inner outer := by
  unfold separatedArmCost
  split_ifs
  · exact hα _ _
  · norm_num

/-- The fixed annular corridors matching `ForestProbes` are paid for by an
explicit constant. Empty probes use exactly the same bound. -/
theorem buffered_armCost_le (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    {C Q g stop u v size : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ stop)
    (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hg : 0 ≤ g)
    (hp : ∀ t, 0 < t → t ≤ stop → 0 < p t)
    (hquasi : ∀ a b, 0 < a → a < b → b ≤ stop → α a b ≤ Q * (p a / p b))
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    separatedArmCost α (8 * max u size) (v/8) ≤
      (Q*C^2*256^g) * Real.exp (g * logarithmicLoss u v size) * (p u / p v) := by
  let M := max u size
  let r := clippedRadius u v size
  have hM : u ≤ M := le_max_left _ _
  have hM0 := hu.trans_le hM
  have hv0 := hu.trans_le huv
  have hr0 := hu.trans_le (le_clippedRadius (size := size) huv)
  have hpu := hp u hu (huv.trans hv)
  have hpv := hp v hv0 hv
  have hC0 : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans hC
  have hQ0 : 0 ≤ Q := (by norm_num : (0:ℝ) ≤ 1).trans hQ
  rw [exponentialLoss_eq_rpow hu huv]
  change separatedArmCost α (8*M) (v/8) ≤ (Q*C^2*256^g) * (r/u)^g * (p u / p v)
  by_cases hprobe : 4*(8*M) < v/8
  · have hraw : 8*M < v/8 := by linarith
    have hMv : M ≤ v := by linarith
    have hr : r = M := min_eq_left hMv
    have ha : u ≤ 8*M := by linarith
    have hav : v/8 ≤ v := by linarith
    have hb0 : 0 < v/8 := by positivity
    have hratio := ratio_compare p hu ha hraw.le hav hv hC0 hpu.le (hp (v/8) hb0 (hav.trans hv)) hpv hlower
    have hbase : ((8*M)/u)*(v/(v/8)) = 64*(r/u) := by
      rw [hr]
      field_simp
      ring
    rw [hbase, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 64) (div_nonneg hr0.le hu.le)] at hratio
    rw [separatedArmCost, ite_eq_left hprobe]
    apply (hquasi (8*M) (v/8) (hu.trans_le ha) hraw (hav.trans hv)).trans
    have h := mul_le_mul_of_nonneg_left hratio hQ0
    have hpow : (64:ℝ)^g ≤ 256^g := Real.rpow_le_rpow (by norm_num) (by norm_num) hg
    have hf : 0 ≤ Q*C^2*(r/u)^g*(p u/p v) := by positivity
    have hh := mul_le_mul_of_nonneg_right hpow hf
    calc
      Q*(p (8*M)/p (v/8)) ≤ 64^g*(Q*C^2*(r/u)^g*(p u/p v)) := by
        convert h using 1
        ring
      _ ≤ _ := by
        convert hh using 1
        ring
  · rw [separatedArmCost, ite_eq_right hprobe]
    have hvr : v ≤ 256*r := by
      by_cases hMv : M ≤ v
      · have hr : r = M := min_eq_left hMv
        rw [hr]
        have h := le_of_not_gt hprobe
        linarith
      · have hr : r = v := min_eq_right (le_of_not_ge hMv)
        rw [hr]
        linarith
    have hbase : v/u ≤ 256*(r/u) := by
      calc
        v/u ≤ (256*r)/u := div_le_div_of_nonneg_right hvr hu.le
        _ = _ := by ring
    have hpow := Real.rpow_le_rpow (div_nonneg hv0.le hu.le) hbase hg
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 256) (div_nonneg hr0.le hu.le)] at hpow
    have hCC : C ≤ Q*C^2 := by
      have hC2 : C ≤ C^2 := by nlinarith
      have hQ2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg C)
      nlinarith
    have hlarge : p v ≤ (Q*C^2*256^g) * (r/u)^g * p u := by
      calc
        p v ≤ C*(v/u)^g*p u := hlower u v hu huv hv
        _ ≤ C*(256^g*(r/u)^g)*p u := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC0) hpu.le
        _ ≤ (Q*C^2)*(256^g*(r/u)^g)*p u := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCC (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg (div_nonneg hr0.le hu.le) _))) hpu.le
        _ = _ := by ring
    have hdiv := div_le_div_of_nonneg_right hlarge hpv.le
    rw [div_self (ne_of_gt hpv)] at hdiv
    convert hdiv using 1
    ring

#print axioms logarithmicLoss_eq_log
#print axioms enlarged_ratio_le
#print axioms enlarged_armCost_le
#print axioms buffered_armCost_le

end ExceptionalTimes.ArmEnlargement

