import ExceptionalTimes.MixedBoundaryProbes
import ExceptionalTimes.HalfArmComparison

open Set

namespace ExceptionalTimes.PairSquareSewing

open ArmEnlargement

theorem profile_outer_move (p : ℝ → ℝ) {a b d C g : ℝ}
    (hpa : 0≤p a) (hpb : 0<p b) (hpd : 0<p d)
    (hgap : p d ≤ C*(d/b)^g*p b) :
    p a/p b ≤ C*(d/b)^g*(p a/p d) := by
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hpb hpd).mpr
  have h := mul_le_mul_of_nonneg_left hgap hpa
  convert h using 1
  ring

noncomputable def splitProfileCost (P : Probe) (q : ℝ × ℝ) (p : ℝ → ℝ) : ℝ :=
  separatedArmCost (fun a b => p a/p b) P.innerRadius (min P.outerRadius (P.distanceTo q/8)) *
  separatedArmCost (fun a b => p a/p b) (8*max P.innerRadius (P.distanceTo q)) (P.outerRadius/8)

/-- All four active/empty cases are covered. The loss is an absolute
constant per life; no unbounded cost depends on the distance to the side. -/
theorem splitProfileCost_le (P : Probe) (q : ℝ × ℝ) (p : ℝ → ℝ)
    {C g : ℝ} (hC : 1≤C) (hg : 0≤g)
    (hp : ∀ t, 0<t → t≤P.outerRadius → 0<p t)
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → p b≤C*(b/a)^g*p a) :
    splitProfileCost P q p ≤ C^3*(8192:ℝ)^g*(p P.innerRadius/p P.outerRadius) := by
  let r := P.innerRadius
  let R := P.outerRadius
  let d := P.distanceTo q
  let b := min R (d/8)
  let a := 8*max r d
  have hr : 0<r := P.inner_pos
  have hR : 0<R := by dsimp [R]; linarith [P.radii,P.inner_pos]
  have hrR : r<R := by dsimp [r,R]; linarith [P.radii,P.inner_pos]
  have hpr := hp r hr hrR.le
  have hpR := hp R hR le_rfl
  have hC0 : 0≤C := by linarith
  have hC23 : C^2≤C^3 := by nlinarith [sq_nonneg (C-1)]
  have hC13 : C≤C^3 := by nlinarith [sq_nonneg (C-1)]
  have hpRatio : 0≤p r/p R := div_nonneg hpr.le hpR.le
  have hPow : 0≤(8192:ℝ)^g := Real.rpow_nonneg (by norm_num) _
  have hfinal {x : ℝ} (hx : x≤C^2*(8192:ℝ)^g*(p r/p R)) :
      x≤C^3*(8192:ℝ)^g*(p r/p R) := by
    exact hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC23 hPow) hpRatio)
  have hone {x y : ℝ} (hx : r≤x) (hxy : x≤y) (hy : y≤R)
      (hscale : (x/r)*(R/y)≤8192) :
      p x/p y≤C^2*(8192:ℝ)^g*(p r/p R) := by
    have hx0 := hr.trans_le hx
    have hy0 := hx0.trans_le hxy
    have ht := ratio_compare p hr hx hxy hy le_rfl hC0 hpr.le
      (hp y hy0 hy) hpR hlower
    have ht' : p x/p y≤C^2*((x/r)*(R/y))^g*(p r/p R) := by
      convert ht using 1
      ring
    have hs := Real.rpow_le_rpow
      (mul_nonneg (div_nonneg hx0.le hr.le) (div_nonneg hR.le hy0.le)) hscale hg
    exact ht'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg C)) hpRatio)
  change separatedArmCost (fun a b => p a/p b) r b *
    separatedArmCost (fun a b => p a/p b) a (R/8) ≤ _
  by_cases hb : BulkPartActive P q
  · have hb' : 4*r<b := hb
    have hbR : b≤R := min_le_left _ _
    have hbd : b≤d/8 := min_le_right _ _
    have hb0 : 0<b := by linarith
    have hrd : r<d := by linarith
    have ha : a=8*d := by dsimp [a]; rw [max_eq_right hrd.le]
    rw [separatedArmCost,ite_eq_left hb']
    by_cases hh : HalfPartActive P q
    · have hh' : 4*a<R/8 := hh
      rw [separatedArmCost,ite_eq_left hh']
      have hdR : d/8≤R := by rw [ha] at hh'; linarith
      have hbe : b=d/8 := min_eq_right hdR
      have hbale : b≤a := by rw [ha,hbe]; linarith
      have haR : a≤R := by linarith
      have he0 : 0<R/8 := by positivity
      have heR : R/8≤R := by linarith
      have hgap := profile_bridge_gap p hpr.le (hp b hb0 hbR) (hp (R/8) he0 heR)
        (hlower b a hb0 hbale haR)
      have htail := profile_outer_move p hpr.le (hp (R/8) he0 heR) hpR
        (hlower (R/8) R he0 heR le_rfl)
      have hscale1 : a/b=64 := by rw [ha,hbe]; field_simp [ne_of_gt (hr.trans hrd)]; norm_num
      have hscale2 : R/(R/8)=8 := by field_simp
      rw [hscale1] at hgap
      rw [hscale2] at htail
      have hmul := mul_le_mul_of_nonneg_left htail (mul_nonneg hC0 (Real.rpow_nonneg (by norm_num : (0:ℝ)≤64) g))
      have hpowprod : (64:ℝ)^g*8^g=(512:ℝ)^g := by
        rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤64) (by norm_num : (0:ℝ)≤8)]
        norm_num
      have hprod : (p r/p b)*(p a/p (R/8))≤C^2*(512:ℝ)^g*(p r/p R) := by
        calc
          _ ≤ C*64^g*(C*8^g*(p r/p R)) := hgap.trans hmul
          _ = _ := by rw [← hpowprod]; ring
      apply hfinal
      exact hprod.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) (by norm_num) hg) (sq_nonneg C)) hpRatio)
    · have hh' : R/8≤4*a := le_of_not_gt hh
      rw [separatedArmCost,ite_eq_right (not_lt.mpr hh'),mul_one]
      apply hfinal
      apply hone le_rfl (by linarith) hbR
      have hRb : R≤2048*b := by
        rcases le_or_gt R (d/8) with h | h
        · have he : b=R := min_eq_left h
          rw [he]
          linarith
        · have he : b=d/8 := min_eq_right h.le
          rw [he,ha] at *
          linarith
      rw [div_self (ne_of_gt hr),one_mul]
      exact (div_le_iff₀ hb0).mpr (by linarith)
  · have hb' : b≤4*r := le_of_not_gt hb
    have hd : d≤32*r := by
      rcases le_or_gt R (d/8) with h | h
      · have he : b=R := min_eq_left h
        rw [he] at hb'
        have hRr := P.radii
        change 4*r<R at hRr
        linarith
      · have he : b=d/8 := min_eq_right h.le
        rw [he] at hb'
        linarith
    have hamax : a≤256*r := by
      have hm : max r d≤32*r := max_le (by linarith) hd
      dsimp [a]
      linarith
    have hra : r≤a := by have := le_max_left r d; dsimp [a]; linarith
    rw [separatedArmCost,ite_eq_right (not_lt.mpr hb'),one_mul]
    by_cases hh : HalfPartActive P q
    · have hh' : 4*a<R/8 := hh
      rw [separatedArmCost,ite_eq_left hh']
      apply hfinal
      apply hone hra (by linarith [hr.trans_le hra]) (by linarith)
      have hscale : R/(R/8)=8 := by field_simp
      rw [hscale]
      have haRatio : a/r≤256 := (div_le_iff₀ hr).mpr (by linarith)
      linarith
    · rw [separatedArmCost,ite_eq_right (show ¬ 4*a<R/8 from hh)]
      have hratio : R/r≤8192 := (div_le_iff₀ hr).mpr (no_active_piece_bounded_ratio P q hb hh)
      have hl := hlower r R hr hrR.le le_rfl
      have hpow := Real.rpow_le_rpow (div_nonneg hR.le hr.le) hratio hg
      have hlarge : p R≤C^3*(8192:ℝ)^g*p r := by
        calc
          p R≤C*(R/r)^g*p r := hl
          _ ≤ C*(8192:ℝ)^g*p r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0) hpr.le
          _ ≤ C^3*(8192:ℝ)^g*p r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC13 hPow) hpr.le
      have ht := div_le_div_of_nonneg_right hlarge hpR.le
      rw [div_self (ne_of_gt hpR)] at ht
      convert ht using 1
      ring

#print axioms splitProfileCost_le

end ExceptionalTimes.PairSquareSewing


