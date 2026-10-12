import ExceptionalTimes.LatticeEmbedding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform radial estimates for the actual embedded triangular lattice. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.LatticeRadial

noncomputable def scaledEmbedding (ε : ℝ) (v : Site) : ℂ :=
  (ε : ℂ) * triangularEmbedding v

theorem scaled_difference_norm (ε : ℝ) (hε : 0 ≤ ε) (v w : Site) :
    ‖scaledEmbedding ε v - scaledEmbedding ε w‖ =
      ε * ‖triangularEmbedding (v - w)‖ := by
  rw [scaledEmbedding, scaledEmbedding, ← mul_sub, ← triangularEmbedding_sub, norm_mul]
  simp [Complex.norm_real, abs_of_nonneg hε]

theorem latticeBox_card (n : ℕ) : (latticeBox n).card = (2 * n + 1) ^ 2 := by
  have hi : ((n : ℤ) + 1 + n).toNat = 2 * n + 1 := by omega
  simp [latticeBox, Finset.card_product, Int.card_Icc, pow_two]
  rw [hi]

/-- The center is an arbitrary complex point, including points off the lattice.
The estimate is independent of the finite set of sites under consideration. -/
theorem scaled_ball_mass_le (s : Finset Site) {ε r : ℝ} (hε : 0 < ε)
    (hr : ε ≤ r) (y : ℂ) (hs : ∀ v ∈ s, ‖scaledEmbedding ε v - y‖ ≤ r) :
    ε ^ 2 * (s.card : ℝ) ≤ 121 * r ^ 2 := by
  classical
  have hr0 : 0 ≤ r := hε.le.trans hr
  by_cases he : s.Nonempty
  · obtain ⟨v₀, hv₀⟩ := he
    let n : ℕ := ⌈4 * r / ε⌉₊
    have hn : 4 * r / ε ≤ (n : ℝ) := Nat.le_ceil _
    have hn' : ε * (n : ℝ) ≤ 4 * r + ε := by
      have h := (Nat.ceil_lt_add_one (show 0 ≤ 4 * r / ε by positivity)).le
      have hm := mul_le_mul_of_nonneg_left h hε.le
      dsimp [n]
      field_simp at hm ⊢
      nlinarith
    have hcoord (v) (hv : v ∈ s) : v - v₀ ∈ latticeBox n := by
      have hd : ε * ‖triangularEmbedding (v - v₀)‖ ≤ 2 * r := by
        rw [← scaled_difference_norm ε hε.le]
        calc
          _ ≤ ‖scaledEmbedding ε v - y‖ + ‖y - scaledEmbedding ε v₀‖ := by
            simpa only [dist_eq_norm] using dist_triangle (scaledEmbedding ε v) y (scaledEmbedding ε v₀)
          _ ≤ 2 * r := by rw [norm_sub_rev y]; linarith [hs v hv, hs v₀ hv₀]
      obtain ⟨hx, hy⟩ := triangularEmbedding_coordinate_bounds (v - v₀)
      have hn₂ : 4 * r ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn
      have hx' : |((v - v₀).1 : ℝ)| ≤ (n : ℝ) := by nlinarith
      have hy' : |((v - v₀).2 : ℝ)| ≤ (n : ℝ) := by nlinarith
      simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
      constructor <;> constructor
      · exact_mod_cast (abs_le.mp hx').1
      · exact_mod_cast (abs_le.mp hx').2
      · exact_mod_cast (abs_le.mp hy').1
      · exact_mod_cast (abs_le.mp hy').2
    have hcard : s.card ≤ (2 * n + 1) ^ 2 := by
      rw [← latticeBox_card]
      calc
        s.card = (s.image (fun v => v - v₀)).card :=
          (Finset.card_image_of_injective s (fun v w h => by
            simpa using congrArg (fun z : Site => z + v₀) h)).symm
        _ ≤ (latticeBox n).card := Finset.card_le_card (by
          intro v hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          exact hcoord w hw)
    have hcast : (s.card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 := by exact_mod_cast hcard
    calc
      _ ≤ ε ^ 2 * (2 * (n : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_left hcast (sq_nonneg ε)
      _ = (ε * (2 * (n : ℝ) + 1)) ^ 2 := by ring
      _ ≤ (11 * r) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
      _ = _ := by ring
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp [hz, sq_nonneg]

noncomputable def clippedKernel (d b g R : ℝ) : ℝ :=
  if max d b < R then (max d b) ^ (-g) else 0

theorem clippedKernel_nonneg (d b g R : ℝ) (hb : 0 ≤ b) :
    0 ≤ clippedKernel d b g R := by
  unfold clippedKernel
  split_ifs
  · exact Real.rpow_nonneg (hb.trans (le_max_right _ _)) _
  · exact le_rfl

theorem clippedKernel_zero_of_le {d b g R : ℝ} (hR : R ≤ b) :
    clippedKernel d b g R = 0 := by
  simp [clippedKernel, not_lt.mpr (hR.trans (le_max_right _ _))]

theorem clippedKernel_step {d b g R : ℝ} (hb : 0 ≤ b) (hg : 0 ≤ g) (hR : 0 < R) :
    clippedKernel d b g R ≤ clippedKernel d b g (R / 2) +
      (if d ≤ R then (R / 2) ^ (-g) else 0) := by
  by_cases h : max d b < R
  · have hd : d ≤ R := (le_max_left d b).trans h.le
    by_cases hh : max d b < R / 2
    · simp only [clippedKernel, ite_eq_left h, ite_eq_left hh, ite_eq_left hd]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    · simp only [clippedKernel, ite_eq_left h, ite_eq_right hh, ite_eq_left hd, zero_add]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_not_gt hh) (neg_nonpos.mpr hg)
  · rw [clippedKernel, ite_eq_right h]
    exact add_nonneg (clippedKernel_nonneg _ _ _ _ hb)
      (by split_ifs; exact Real.rpow_nonneg (by positivity) _; exact le_rfl)

noncomputable def clippedSum (s : Finset Site) (ε b g R : ℝ) (y : ℂ) : ℝ :=
  ε ^ 2 * ∑ v ∈ s, clippedKernel ‖scaledEmbedding ε v - y‖ b g R

theorem shell_power {R : ℝ} (hR : 0 < R) (g : ℝ) :
    R ^ 2 * (R / 2) ^ (-g) = (2 : ℝ) ^ g * R ^ (2 - g) := by
  rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul]
  rw [← Real.rpow_natCast R 2, ← mul_assoc, ← Real.rpow_add hR]
  norm_num
  rw [show (2 : ℝ) + -g = 2-g by ring]
  ring

theorem clippedSum_step (s : Finset Site) {ε b g R : ℝ} (y : ℂ)
    (hε : 0 < ε) (hb : ε ≤ b) (hbR : b < R) (hg : 0 ≤ g) :
    clippedSum s ε b g R y ≤ clippedSum s ε b g (R / 2) y +
      (121 * (2 : ℝ) ^ g) * R ^ (2 - g) := by
  have hb0 : 0 ≤ b := hε.le.trans hb
  have hR : 0 < R := hε.trans_le (hb.trans hbR.le)
  let ball := s.filter (fun v => ‖scaledEmbedding ε v - y‖ ≤ R)
  have hm : ε ^ 2 * (ball.card : ℝ) ≤ 121 * R ^ 2 :=
    scaled_ball_mass_le ball hε (hb.trans hbR.le) y
      (fun v hv => (Finset.mem_filter.mp hv).2)
  have hsum : (∑ v ∈ s, clippedKernel ‖scaledEmbedding ε v - y‖ b g R) ≤
      (∑ v ∈ s, clippedKernel ‖scaledEmbedding ε v - y‖ b g (R/2)) +
      (ball.card : ℝ) * (R/2) ^ (-g) := by
    calc
      _ ≤ ∑ v ∈ s, (clippedKernel ‖scaledEmbedding ε v - y‖ b g (R/2) +
          if ‖scaledEmbedding ε v - y‖ ≤ R then (R/2)^(-g) else 0) :=
        Finset.sum_le_sum (fun v hv => clippedKernel_step hb0 hg hR)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [ball, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hk0 : 0 ≤ (R/2)^(-g) := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ε^2 * ((∑ v ∈ s, clippedKernel ‖scaledEmbedding ε v-y‖ b g (R/2)) +
        (ball.card : ℝ) * (R/2)^(-g)) := mul_le_mul_of_nonneg_left hsum (sq_nonneg ε)
    _ = clippedSum s ε b g (R/2) y + (ε^2 * (ball.card : ℝ)) * (R/2)^(-g) := by
      unfold clippedSum; ring
    _ ≤ clippedSum s ε b g (R/2) y + (121 * R^2) * (R/2)^(-g) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hm hk0)
    _ = _ := by rw [mul_assoc 121, shell_power hR]; ring

noncomputable def radialConstant (g : ℝ) : ℝ :=
  121 * (2 : ℝ) ^ g / (1 - (1 / 2 : ℝ) ^ (2 - g))

/-- The clipped one-edge estimate, including the atom at the center and an
arbitrary center off the lattice. No ball-growth hypothesis is supplied: it was
proved above from integer-coordinate counting. -/
theorem clippedSum_le (s : Finset Site) {ε b g R : ℝ} (y : ℂ)
    (hε : 0 < ε) (hb : ε ≤ b) (hg : 0 ≤ g) (hg2 : g < 2) (hR : 0 < R) :
    clippedSum s ε b g R y ≤ radialConstant g * R ^ (2 - g) := by
  have hb0 : 0 < b := hε.trans_le hb
  let q : ℝ := (1/2 : ℝ) ^ (2-g)
  let A : ℝ := 121 * (2 : ℝ) ^ g
  let D : ℝ := radialConstant g
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hD : 0 ≤ D := by
    dsimp [D, radialConstant]
    exact div_nonneg (by positivity) (sub_nonneg.mpr hq.le)
  have heq : D * q + A = D := by
    have hden : 1-q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
    dsimp [D, radialConstant, A, q] at *
    field_simp
    ring
  have hz {r : ℝ} (hr : r ≤ b) : clippedSum s ε b g r y = 0 := by
    simp only [clippedSum, clippedKernel_zero_of_le hr, Finset.sum_const_zero, mul_zero]
  have hind (n : ℕ) : ∀ r : ℝ, 0 < r → r ≤ (2 : ℝ)^n * b →
      clippedSum s ε b g r y ≤ D * r ^ (2-g) := by
    induction n with
    | zero =>
      intro r hr hn
      have hrb : r ≤ b := by simpa using hn
      rw [hz hrb]
      exact mul_nonneg hD (Real.rpow_nonneg hr.le _)
    | succ n ih =>
      intro r hr hn
      by_cases hrb : r ≤ b
      · rw [hz hrb]
        exact mul_nonneg hD (Real.rpow_nonneg hr.le _)
      · have hhalf : r/2 ≤ (2:ℝ)^n*b := by rw [pow_succ] at hn; nlinarith
        have hh := ih (r/2) (by positivity) hhalf
        have hp : (r/2) ^ (2-g) = r ^ (2-g) * q := by
          rw [show r/2 = r*(1/2) by ring, Real.mul_rpow hr.le (by norm_num)]
        calc
          _ ≤ clippedSum s ε b g (r/2) y + A * r^(2-g) :=
            clippedSum_step s y hε hb (lt_of_not_ge hrb) hg
          _ ≤ D*(r/2)^(2-g) + A*r^(2-g) := add_le_add hh le_rfl
          _ = (D*q+A)*r^(2-g) := by rw [hp]; ring
          _ = D*r^(2-g) := by rw [heq]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R/b) (by norm_num : (1:ℝ)<2)
  exact hind n R hR (le_of_lt ((div_lt_iff₀ hb0).mp hn))

/-- Static four-arm exponent input in the exact form used by the forest
argument. The range on the exponent loss is precisely the integrability range. -/
theorem clippedSum_four_arm (s : Finset Site) {ε b ζ R : ℝ} (y : ℂ)
    (hε : 0 < ε) (hb : ε ≤ b) (hζ : 0 ≤ ζ) (hζ' : ζ < 3/4) (hR : 0 < R) :
    clippedSum s ε b (5/4+ζ) R y ≤
      radialConstant (5/4+ζ) * R ^ (3/4-ζ) := by
  have he : (2 : ℝ) - (5/4+ζ) = 3/4-ζ := by ring
  simpa only [he] using clippedSum_le s y hε hb (by linarith : 0 ≤ (5/4:ℝ)+ζ)
    (by linarith : (5/4:ℝ)+ζ<2) hR

theorem clippedKernel_change_clip {d ε b g R : ℝ} (hε : 0 < ε)
    (hb : 0 < b) (hg : 0 ≤ g) :
    clippedKernel d b g R ≤ clippedKernel d ε g R +
      (if d ≤ ε then b ^ (-g) else 0) := by
  by_cases h : max d b < R
  · by_cases hd : d ≤ ε
    · rw [clippedKernel, ite_eq_left h, ite_eq_left hd]
      exact (Real.rpow_le_rpow_of_nonpos hb (le_max_right _ _) (neg_nonpos.mpr hg)).trans
        (le_add_of_nonneg_left (clippedKernel_nonneg d ε g R hε.le))
    · have hd' : ε ≤ d := (lt_of_not_ge hd).le
      have hdR : d < R := lt_of_le_of_lt (le_max_left _ _) h
      simp only [clippedKernel, ite_eq_left h, max_eq_left hd', ite_eq_left hdR, ite_eq_right hd, add_zero]
      exact Real.rpow_le_rpow_of_nonpos (hε.trans_le hd') (le_max_left _ _)
        (neg_nonpos.mpr hg)
  · rw [clippedKernel, ite_eq_right h]
    exact add_nonneg (clippedKernel_nonneg _ _ _ _ hε.le)
      (by split_ifs; exact Real.rpow_nonneg hb.le _; exact le_rfl)

/-- The manuscript's general cutoff condition `b ≥ c ε`, with an explicit
constant depending only on `c` and the exponent. -/
theorem clippedSum_le_of_clip_ratio (s : Finset Site) {ε b c g R : ℝ} (y : ℂ)
    (hε : 0 < ε) (hc : 0 < c) (hb : c * ε ≤ b)
    (hg : 0 ≤ g) (hg2 : g < 2) (hR : 0 < R) :
    clippedSum s ε b g R y ≤
      (radialConstant g + 121 / c ^ 2) * R ^ (2-g) := by
  have hb0 : 0 < b := (mul_pos hc hε).trans_le hb
  have hD : 0 ≤ radialConstant g := by
    unfold radialConstant
    exact div_nonneg (by positivity) (sub_nonneg.mpr
      (Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith : 0 < 2-g)).le)
  by_cases hbR : R ≤ b
  · have hz : clippedSum s ε b g R y = 0 := by
      simp only [clippedSum, clippedKernel_zero_of_le hbR, Finset.sum_const_zero, mul_zero]
    rw [hz]
    exact mul_nonneg (add_nonneg hD (by positivity)) (Real.rpow_nonneg hR.le _)
  have hbR' : b ≤ R := (lt_of_not_ge hbR).le
  let ball := s.filter (fun v => ‖scaledEmbedding ε v - y‖ ≤ ε)
  have hm := scaled_ball_mass_le ball hε le_rfl y
    (fun v hv => (Finset.mem_filter.mp hv).2)
  have hsum : clippedSum s ε b g R y ≤
      clippedSum s ε ε g R y + (ε^2 * (ball.card : ℝ)) * b^(-g) := by
    have hh := Finset.sum_le_sum (s := s) (fun v hv =>
      clippedKernel_change_clip (d := ‖scaledEmbedding ε v-y‖) (R := R) hε hb0 hg)
    simp only [Finset.sum_add_distrib] at hh
    have he : (∑ v ∈ s, if ‖scaledEmbedding ε v-y‖ ≤ ε then b^(-g) else 0) =
        (ball.card : ℝ) * b^(-g) := by
      simp only [ball, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [he] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    simpa only [mul_add, ← mul_assoc, clippedSum] using hh'
  have hsq : ε^2 ≤ b^2 / c^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    have hh := pow_le_pow_left₀ (mul_nonneg hc.le hε.le) hb 2
    nlinarith [hh]
  have hp : b^2 * b^(-g) = b^(2-g) := by
    rw [← Real.rpow_natCast b 2, ← Real.rpow_add hb0]
    norm_num [sub_eq_add_neg]
  have hpower : b^(2-g) ≤ R^(2-g) := Real.rpow_le_rpow hb0.le hbR' (by linarith)
  calc
    _ ≤ clippedSum s ε ε g R y + (121*ε^2)*b^(-g) :=
      hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hm
        (Real.rpow_nonneg hb0.le _)))
    _ ≤ radialConstant g * R^(2-g) + (121*(b^2/c^2))*b^(-g) :=
      add_le_add (clippedSum_le s y hε le_rfl hg hg2 hR)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
          (Real.rpow_nonneg hb0.le _))
    _ = radialConstant g * R^(2-g) + (121/c^2)*b^(2-g) := by rw [← hp]; ring
    _ ≤ radialConstant g * R^(2-g) + (121/c^2)*R^(2-g) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower (by positivity))
    _ = _ := by ring

#print axioms scaled_ball_mass_le
#print axioms clippedSum_step
#print axioms clippedSum_le
#print axioms clippedSum_four_arm
#print axioms clippedSum_le_of_clip_ratio

end ExceptionalTimes.LatticeRadial

