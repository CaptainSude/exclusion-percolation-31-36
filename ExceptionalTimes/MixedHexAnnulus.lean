import ExceptionalTimes.HexRoundAnnulus

open Set
open scoped Classical

namespace ExceptionalTimes.Annulus

theorem norm_planeMap_le_two_hexGauge (p : ℝ × ℝ) :
    ‖HexTiling.planeMap p‖ ≤ 2*hexGauge p := by
  have hx : |p.1| ≤ hexGauge p := (le_max_left _ _).trans (le_max_left _ _)
  have hy : |p.2| ≤ hexGauge p := (le_max_right _ _).trans (le_max_left _ _)
  linarith [HexTiling.planeMap_norm_le_coordinates p]

/-- Along the ray through p, the Euclidean radius at which the ray meets
the hexagon of gauge r. This is a direction-dependent positive radius. -/
noncomputable def hexRayRadius (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  r*‖HexTiling.planeMap p‖/hexGauge p

theorem hexRayRadius_pos {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ} (hp : p ≠ 0) :
    0 < hexRayRadius r p :=
  div_pos (mul_pos hr (norm_pos_iff.mpr (planeMap_ne_zero hp))) (hexGauge_pos hp)

theorem hexRayRadius_le {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ} (hp : p ≠ 0) :
    hexRayRadius r p ≤ 2*r := by
  unfold hexRayRadius
  apply (div_le_iff₀ (hexGauge_pos hp)).mpr
  nlinarith [norm_planeMap_le_two_hexGauge p]

theorem hexRayRadius_smul (r : ℝ) {a : ℝ} (ha : 0 < a) (p : ℝ × ℝ) :
    hexRayRadius r (a • p) = hexRayRadius r p := by
  simp only [hexRayRadius,planeMap_smul,norm_smul,Real.norm_eq_abs,hexGauge_smul,abs_of_pos ha]
  by_cases hg : hexGauge p = 0
  · simp [hg]
  · field_simp

def mixedHexAnnulus (r S : ℝ) : Set (ℝ × ℝ) :=
  {p | r ≤ hexGauge p ∧ ‖HexTiling.planeMap p‖ ≤ S}

theorem mixedHexAnnulus_ne_zero {r S : ℝ} (hr : 0 < r) (p : mixedHexAnnulus r S) :
    (p : ℝ × ℝ) ≠ 0 := by
  intro hp
  have h := p.property.1
  rw [hp,(hexGauge_eq_zero_iff 0).mpr rfl] at h
  linarith

theorem hexRayRadius_le_norm {r S : ℝ} (hr : 0 < r) (p : mixedHexAnnulus r S) :
    hexRayRadius r p ≤ ‖HexTiling.planeMap p‖ := by
  unfold hexRayRadius
  apply (div_le_iff₀ (hexGauge_pos (mixedHexAnnulus_ne_zero hr p))).mpr
  nlinarith [p.property.1,norm_nonneg (HexTiling.planeMap p)]

/-- Radial affine interpolation fixes the outer circle and sends the
inner hexagonal boundary to the circle of radius r. -/
noncomputable def mixedRoundRadius (r S : ℝ) (p : ℝ × ℝ) : ℝ :=
  r+(‖HexTiling.planeMap p‖-hexRayRadius r p)/(S-hexRayRadius r p)*(S-r)

noncomputable def mixedUnroundRadius (r S : ℝ) (p : ℝ × ℝ) : ℝ :=
  hexRayRadius r p+(‖HexTiling.planeMap p‖-r)/(S-r)*(S-hexRayRadius r p)

noncomputable def mixedRound (r S : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (mixedRoundRadius r S p/‖HexTiling.planeMap p‖) • p

noncomputable def mixedUnround (r S : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (mixedUnroundRadius r S p/‖HexTiling.planeMap p‖) • p

theorem mixedRoundRadius_bounds {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) : r ≤ mixedRoundRadius r S p ∧ mixedRoundRadius r S p ≤ S := by
  have ha := hexRayRadius_le hr (mixedHexAnnulus_ne_zero hr p)
  have haN := hexRayRadius_le_norm hr p
  have haS : 0 < S-hexRayRadius r p := by linarith
  have hf0 : 0 ≤ (‖HexTiling.planeMap p‖-hexRayRadius r p)/(S-hexRayRadius r p) :=
    div_nonneg (sub_nonneg.mpr haN) haS.le
  have hf1 : (‖HexTiling.planeMap p‖-hexRayRadius r p)/(S-hexRayRadius r p) ≤ 1 := by
    apply (div_le_iff₀ haS).mpr
    linarith [p.property.2]
  unfold mixedRoundRadius
  constructor <;> nlinarith

theorem mixedRoundRadius_inner {r S : ℝ} {p : ℝ × ℝ}
    (hp : hexGauge p = r) (hr : r ≠ 0) : mixedRoundRadius r S p = r := by
  have ha : hexRayRadius r p = ‖HexTiling.planeMap p‖ := by
    unfold hexRayRadius
    rw [hp]
    field_simp
  simp [mixedRoundRadius,ha]

theorem mixedRoundRadius_outer {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    {p : ℝ × ℝ} (hp : p ≠ 0) (hN : ‖HexTiling.planeMap p‖ = S) :
    mixedRoundRadius r S p = S := by
  have hpos : 0 < S-hexRayRadius r p := by linarith [hexRayRadius_le hr hp]
  simp [mixedRoundRadius,hN,hpos.ne']

#print axioms mixedRoundRadius_bounds
#print axioms mixedRoundRadius_inner
#print axioms mixedRoundRadius_outer

theorem norm_planeMap_mixedRound {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) :
    ‖HexTiling.planeMap (mixedRound r S p)‖ = mixedRoundRadius r S p := by
  have hN := norm_pos_iff.mpr (planeMap_ne_zero (mixedHexAnnulus_ne_zero hr p))
  have hT : 0 < mixedRoundRadius r S p := hr.trans_le (mixedRoundRadius_bounds hr hS p).1
  rw [mixedRound,planeMap_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hT hN)]
  exact div_mul_cancel₀ _ hN.ne'

theorem hexRayRadius_mixedRound {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) : hexRayRadius r (mixedRound r S p) = hexRayRadius r p := by
  have hN := norm_pos_iff.mpr (planeMap_ne_zero (mixedHexAnnulus_ne_zero hr p))
  have hT : 0 < mixedRoundRadius r S p := hr.trans_le (mixedRoundRadius_bounds hr hS p).1
  exact hexRayRadius_smul r (div_pos hT hN) p

theorem mixedUnroundRadius_round {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) :
    mixedUnroundRadius r S (mixedRound r S p) = ‖HexTiling.planeMap p‖ := by
  have hA : S-hexRayRadius r p ≠ 0 := by
    have := hexRayRadius_le hr (mixedHexAnnulus_ne_zero hr p)
    linarith
  have hB : S-r ≠ 0 := by linarith
  unfold mixedUnroundRadius
  rw [hexRayRadius_mixedRound hr hS p,norm_planeMap_mixedRound hr hS p]
  unfold mixedRoundRadius
  field_simp
  ring

theorem mixedUnround_mixedRound {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) : mixedUnround r S (mixedRound r S p) = p := by
  have hN := norm_pos_iff.mpr (planeMap_ne_zero (mixedHexAnnulus_ne_zero hr p))
  have hT : 0 < mixedRoundRadius r S p := hr.trans_le (mixedRoundRadius_bounds hr hS p).1
  unfold mixedUnround
  rw [mixedUnroundRadius_round hr hS p,norm_planeMap_mixedRound hr hS p,mixedRound,smul_smul]
  have hcoeff : (‖HexTiling.planeMap p‖/mixedRoundRadius r S p)*
      (mixedRoundRadius r S p/‖HexTiling.planeMap p‖) = 1 := by field_simp
  rw [hcoeff,one_smul]

theorem mixedUnroundRadius_bounds {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : ℝ × ℝ) (hp : r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S) :
    hexRayRadius r p ≤ mixedUnroundRadius r S p ∧ mixedUnroundRadius r S p ≤ S := by
  have hN : 0 < ‖HexTiling.planeMap p‖ := hr.trans_le hp.1
  have hne : p ≠ 0 := by intro he; rw [he,planeMap_zero,norm_zero] at hN; linarith
  have ha := hexRayRadius_le hr hne
  have hden : 0 < S-r := by linarith
  have hf0 : 0 ≤ (‖HexTiling.planeMap p‖-r)/(S-r) :=
    div_nonneg (sub_nonneg.mpr hp.1) hden.le
  have hf1 : (‖HexTiling.planeMap p‖-r)/(S-r) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith [hp.2]
  unfold mixedUnroundRadius
  constructor <;> nlinarith

theorem mixedUnroundRadius_pos {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : ℝ × ℝ) (hp : r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S) :
    0 < mixedUnroundRadius r S p := by
  have hne : p ≠ 0 := by
    intro he
    have := hp.1
    rw [he,planeMap_zero,norm_zero] at this
    linarith
  exact (hexRayRadius_pos hr hne).trans_le (mixedUnroundRadius_bounds hr hS p hp).1

theorem norm_planeMap_mixedUnround {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : ℝ × ℝ) (hp : r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S) :
    ‖HexTiling.planeMap (mixedUnround r S p)‖ = mixedUnroundRadius r S p := by
  have hN : 0 < ‖HexTiling.planeMap p‖ := hr.trans_le hp.1
  have hU := mixedUnroundRadius_pos hr hS p hp
  rw [mixedUnround,planeMap_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hU hN)]
  exact div_mul_cancel₀ _ hN.ne'

theorem hexRayRadius_mixedUnround {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : ℝ × ℝ) (hp : r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S) :
    hexRayRadius r (mixedUnround r S p) = hexRayRadius r p := by
  have hN : 0 < ‖HexTiling.planeMap p‖ := hr.trans_le hp.1
  exact hexRayRadius_smul r (div_pos (mixedUnroundRadius_pos hr hS p hp) hN) p

theorem mixedUnround_mem {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : ℝ × ℝ) (hp : r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S) :
    mixedUnround r S p ∈ mixedHexAnnulus r S := by
  have hN : 0 < ‖HexTiling.planeMap p‖ := hr.trans_le hp.1
  have hne : p ≠ 0 := by intro he; rw [he,planeMap_zero,norm_zero] at hN; linarith
  have hG := hexGauge_pos hne
  have hU := mixedUnroundRadius_pos hr hS p hp
  have hb := mixedUnroundRadius_bounds hr hS p hp
  constructor
  · rw [mixedUnround,hexGauge_smul,abs_of_pos (div_pos hU hN)]
    have hA : r*‖HexTiling.planeMap p‖ ≤ mixedUnroundRadius r S p*hexGauge p :=
      (div_le_iff₀ hG).mp hb.1
    calc r ≤ (mixedUnroundRadius r S p*hexGauge p)/‖HexTiling.planeMap p‖ :=
        (le_div_iff₀ hN).mpr hA
      _ = mixedUnroundRadius r S p/‖HexTiling.planeMap p‖*hexGauge p := by ring
  · rw [norm_planeMap_mixedUnround hr hS p hp]
    exact hb.2

theorem mixedRoundRadius_unround {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : ℝ × ℝ) (hp : r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S) :
    mixedRoundRadius r S (mixedUnround r S p) = ‖HexTiling.planeMap p‖ := by
  have hne : p ≠ 0 := by
    intro he
    have := hp.1
    rw [he,planeMap_zero,norm_zero] at this
    linarith
  have hA : S-hexRayRadius r p ≠ 0 := by linarith [hexRayRadius_le hr hne]
  have hB : S-r ≠ 0 := by linarith
  unfold mixedRoundRadius
  rw [hexRayRadius_mixedUnround hr hS p hp,norm_planeMap_mixedUnround hr hS p hp]
  unfold mixedUnroundRadius
  field_simp
  ring

theorem mixedRound_mixedUnround {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : ℝ × ℝ) (hp : r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S) :
    mixedRound r S (mixedUnround r S p) = p := by
  have hN : 0 < ‖HexTiling.planeMap p‖ := hr.trans_le hp.1
  have hU := mixedUnroundRadius_pos hr hS p hp
  unfold mixedRound
  rw [mixedRoundRadius_unround hr hS p hp,norm_planeMap_mixedUnround hr hS p hp,
    mixedUnround,smul_smul]
  have hcoeff : (‖HexTiling.planeMap p‖/mixedUnroundRadius r S p)*
      (mixedUnroundRadius r S p/‖HexTiling.planeMap p‖) = 1 := by field_simp
  rw [hcoeff,one_smul]

#print axioms mixedUnround_mixedRound
#print axioms mixedUnround_mem
#print axioms mixedRound_mixedUnround

theorem continuousOn_hexRayRadius (r : ℝ) (D : Set (ℝ × ℝ))
    (hD : ∀ p ∈ D, p ≠ 0) : ContinuousOn (hexRayRadius r) D :=
  (continuousOn_const.mul HexTiling.continuous_planeMap.norm.continuousOn).div
    continuous_hexGauge.continuousOn (fun p hp => (hexGauge_pos (hD p hp)).ne')

theorem continuousOn_mixedRound {r S : ℝ} (hr : 0 < r) (hS : 2*r < S) :
    ContinuousOn (mixedRound r S) (mixedHexAnnulus r S) := by
  have hne : ∀ p ∈ mixedHexAnnulus r S, p ≠ 0 :=
    fun p hp => mixedHexAnnulus_ne_zero hr ⟨p,hp⟩
  have hc := continuousOn_hexRayRadius r (mixedHexAnnulus r S) hne
  have hn := HexTiling.continuous_planeMap.norm.continuousOn (s := mixedHexAnnulus r S)
  have hd : ∀ p ∈ mixedHexAnnulus r S, S-hexRayRadius r p ≠ 0 := by
    intro p hp
    have := hexRayRadius_le hr (hne p hp)
    linarith
  exact (continuousOn_const.add (((hn.sub hc).div (continuousOn_const.sub hc) hd).mul
    continuousOn_const)).div hn (fun p hp => (norm_pos_iff.mpr (planeMap_ne_zero (hne p hp))).ne')
      |>.smul continuousOn_id

theorem continuousOn_mixedUnround {r S : ℝ} (hr : 0 < r) (hS : 2*r < S) :
    ContinuousOn (mixedUnround r S) {p | r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S} := by
  let D : Set (ℝ × ℝ) := {p | r ≤ ‖HexTiling.planeMap p‖ ∧ ‖HexTiling.planeMap p‖ ≤ S}
  have hne : ∀ p ∈ D, p ≠ 0 := by
    intro p hp he
    have := hp.1
    rw [he,planeMap_zero,norm_zero] at this
    linarith
  have hc := continuousOn_hexRayRadius r D hne
  have hn := HexTiling.continuous_planeMap.norm.continuousOn (s := D)
  have hd : S-r ≠ 0 := by linarith
  exact (hc.add (((hn.sub continuousOn_const).div_const (S-r)).mul
    (continuousOn_const.sub hc))).div hn
      (fun p hp => (norm_pos_iff.mpr (planeMap_ne_zero (hne p hp))).ne')
        |>.smul continuousOn_id

/-- The mixed annulus between an inner hexagonal cut and an outer
Euclidean circle is explicitly homeomorphic to a round annulus. The
strict bound 2r<S leaves the entire inner hexagon inside the circle. -/
noncomputable def mixedHexAnnulusHomeomorph (r S : ℝ) (hr : 0 < r) (hS : 2*r < S) :
    mixedHexAnnulus r S ≃ₜ roundAnnulus r S where
  toFun p := ⟨HexTiling.planeMap (mixedRound r S p),by
    change r ≤ ‖HexTiling.planeMap (mixedRound r S p)‖ ∧ ‖HexTiling.planeMap (mixedRound r S p)‖ ≤ S
    rw [norm_planeMap_mixedRound hr hS p]
    exact mixedRoundRadius_bounds hr hS p⟩
  invFun z := ⟨mixedUnround r S (planeInverse z),mixedUnround_mem hr hS _ (by
    rw [planeMap_planeInverse]
    exact z.property)⟩
  left_inv p := by
    apply Subtype.ext
    change mixedUnround r S (planeInverse (HexTiling.planeMap (mixedRound r S p))) = p
    rw [planeInverse_planeMap]
    exact mixedUnround_mixedRound hr hS p
  right_inv z := by
    apply Subtype.ext
    change HexTiling.planeMap (mixedRound r S (mixedUnround r S (planeInverse z))) = z
    rw [mixedRound_mixedUnround hr hS _ (by rw [planeMap_planeInverse]; exact z.property),
      planeMap_planeInverse]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact HexTiling.continuous_planeMap.comp
      ((continuousOn_mixedRound hr hS).comp_continuous continuous_subtype_val Subtype.prop)
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun z : roundAnnulus r S => planeInverse z) :=
      planeMapHomeomorph.symm.continuous.comp continuous_subtype_val
    exact (continuousOn_mixedUnround hr hS).comp_continuous hc (fun z => by
      change r ≤ ‖HexTiling.planeMap (planeInverse z)‖ ∧ ‖HexTiling.planeMap (planeInverse z)‖ ≤ S
      rw [planeMap_planeInverse]
      exact z.property)

#print axioms mixedHexAnnulusHomeomorph

theorem mixedRoundRadius_strict {r S : ℝ} (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S)
    (hin : r < hexGauge p) (hout : ‖HexTiling.planeMap p‖ < S) :
    r < mixedRoundRadius r S p ∧ mixedRoundRadius r S p < S := by
  have hG := hexGauge_pos (mixedHexAnnulus_ne_zero hr p)
  have hN := norm_pos_iff.mpr (planeMap_ne_zero (mixedHexAnnulus_ne_zero hr p))
  have ha := hexRayRadius_le hr (mixedHexAnnulus_ne_zero hr p)
  have haN : hexRayRadius r p < ‖HexTiling.planeMap p‖ := by
    apply (div_lt_iff₀ hG).mpr
    nlinarith
  have haS : 0 < S-hexRayRadius r p := by linarith
  have hf0 : 0 < (‖HexTiling.planeMap p‖-hexRayRadius r p)/(S-hexRayRadius r p) :=
    div_pos (sub_pos.mpr haN) haS
  have hf1 : (‖HexTiling.planeMap p‖-hexRayRadius r p)/(S-hexRayRadius r p) < 1 := by
    apply (div_lt_iff₀ haS).mpr
    linarith
  unfold mixedRoundRadius
  constructor <;> nlinarith

theorem mixedHexAnnulusHomeomorph_arg (r S : ℝ) (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) :
    Complex.arg (mixedHexAnnulusHomeomorph r S hr hS p : ℂ) =
      Complex.arg (HexTiling.planeMap p) := by
  change Complex.arg (HexTiling.planeMap (mixedRound r S p)) = _
  rw [mixedRound,planeMap_smul]
  have hN := norm_pos_iff.mpr (planeMap_ne_zero (mixedHexAnnulus_ne_zero hr p))
  have hT : 0 < mixedRoundRadius r S p := hr.trans_le (mixedRoundRadius_bounds hr hS p).1
  exact Complex.arg_real_mul _ (div_pos hT hN)

theorem mixedHexAnnulusHomeomorph_inner (r S : ℝ) (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) (hp : hexGauge p = r) :
    ‖(mixedHexAnnulusHomeomorph r S hr hS p : ℂ)‖ = r := by
  change ‖HexTiling.planeMap (mixedRound r S p)‖ = r
  rw [norm_planeMap_mixedRound hr hS p,mixedRoundRadius_inner hp hr.ne']

theorem mixedHexAnnulusHomeomorph_outer (r S : ℝ) (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) (hp : ‖HexTiling.planeMap p‖ = S) :
    (mixedHexAnnulusHomeomorph r S hr hS p : ℂ) = HexTiling.planeMap p := by
  change HexTiling.planeMap (mixedRound r S p) = _
  unfold mixedRound
  rw [mixedRoundRadius_outer hr hS (mixedHexAnnulus_ne_zero hr p) hp,hp,
    div_self (by linarith : S ≠ 0),one_smul]

theorem mixedHexAnnulusHomeomorph_strict (r S : ℝ) (hr : 0 < r) (hS : 2*r < S)
    (p : mixedHexAnnulus r S) (hin : r < hexGauge p) (hout : ‖HexTiling.planeMap p‖ < S) :
    r < ‖(mixedHexAnnulusHomeomorph r S hr hS p : ℂ)‖ ∧
      ‖(mixedHexAnnulusHomeomorph r S hr hS p : ℂ)‖ < S := by
  change r < ‖HexTiling.planeMap (mixedRound r S p)‖ ∧
    ‖HexTiling.planeMap (mixedRound r S p)‖ < S
  rw [norm_planeMap_mixedRound hr hS p]
  exact mixedRoundRadius_strict hr hS p hin hout

#print axioms mixedHexAnnulusHomeomorph_arg
#print axioms mixedHexAnnulusHomeomorph_inner
#print axioms mixedHexAnnulusHomeomorph_outer
#print axioms mixedHexAnnulusHomeomorph_strict

end ExceptionalTimes.Annulus
