import ExceptionalTimes.HexTiling
import ExceptionalTimes.Annulus
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Set
open scoped Classical

namespace ExceptionalTimes.Annulus

/-- Continuous extension of the exact axial lattice radius. -/
def hexGauge (p : ℝ × ℝ) : ℝ := max (max |p.1| |p.2|) |p.1+p.2|

theorem hexGauge_nonneg (p : ℝ × ℝ) : 0 ≤ hexGauge p :=
  (abs_nonneg p.1).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem hexGauge_eq_zero_iff (p : ℝ × ℝ) : hexGauge p = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hx : |p.1| ≤ 0 := h ▸ (le_max_left _ _).trans (le_max_left _ _)
    have hy : |p.2| ≤ 0 := h ▸ (le_max_right _ _).trans (le_max_left _ _)
    exact Prod.ext (abs_eq_zero.mp (le_antisymm hx (abs_nonneg _)))
      (abs_eq_zero.mp (le_antisymm hy (abs_nonneg _)))
  · rintro rfl
    simp [hexGauge]

theorem hexGauge_pos {p : ℝ × ℝ} (hp : p ≠ 0) : 0 < hexGauge p :=
  lt_of_le_of_ne (hexGauge_nonneg p) (Ne.symm ((hexGauge_eq_zero_iff p).not.mpr hp))

theorem continuous_hexGauge : Continuous hexGauge := by unfold hexGauge; fun_prop

theorem hexGauge_smul (a : ℝ) (p : ℝ × ℝ) : hexGauge (a • p) = |a| * hexGauge p := by
  change max (max |a*p.1| |a*p.2|) |a*p.1+a*p.2| = |a| * hexGauge p
  simp only [hexGauge,←mul_add,abs_mul]
  rw [mul_max_of_nonneg _ _ (abs_nonneg a),mul_max_of_nonneg _ _ (abs_nonneg a)]

theorem hexGauge_site (v : Site) : hexGauge ((v.1:ℝ),(v.2:ℝ)) = (hexRadius v : ℝ) := by
  simp only [hexGauge,hexRadius,Int.cast_max,Int.cast_abs,Int.cast_add]

theorem planeMap_smul (a : ℝ) (p : ℝ × ℝ) :
    HexTiling.planeMap (a • p) = a • HexTiling.planeMap p := by
  apply Complex.ext <;> simp [HexTiling.planeMap] <;> ring

theorem planeMap_zero : HexTiling.planeMap 0 = 0 := by
  apply Complex.ext <;> simp [HexTiling.planeMap]

theorem planeMap_ne_zero {p : ℝ × ℝ} (hp : p ≠ 0) : HexTiling.planeMap p ≠ 0 := by
  intro h
  exact hp (HexTiling.planeMap_injective (h.trans planeMap_zero.symm))

/-- Positive radial map turning every axial hexagon into a Euclidean
circle after applying the actual triangular embedding. -/
noncomputable def roundHex (p : ℝ × ℝ) : ℝ × ℝ :=
  (hexGauge p / ‖HexTiling.planeMap p‖) • p

noncomputable def unroundHex (p : ℝ × ℝ) : ℝ × ℝ :=
  (‖HexTiling.planeMap p‖ / hexGauge p) • p

theorem roundHex_ne_zero {p : ℝ × ℝ} (hp : p ≠ 0) : roundHex p ≠ 0 :=
  smul_ne_zero (div_pos (hexGauge_pos hp) (norm_pos_iff.mpr (planeMap_ne_zero hp))).ne' hp

theorem unroundHex_ne_zero {p : ℝ × ℝ} (hp : p ≠ 0) : unroundHex p ≠ 0 :=
  smul_ne_zero (div_pos (norm_pos_iff.mpr (planeMap_ne_zero hp)) (hexGauge_pos hp)).ne' hp

theorem norm_planeMap_roundHex (p : ℝ × ℝ) :
    ‖HexTiling.planeMap (roundHex p)‖ = hexGauge p := by
  by_cases hp : p = 0
  · subst p
    simp [roundHex,hexGauge,planeMap_zero]
  · have hg := hexGauge_pos hp
    have hn := norm_pos_iff.mpr (planeMap_ne_zero hp)
    rw [roundHex,planeMap_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hg hn)]
    exact div_mul_cancel₀ _ hn.ne'

theorem unroundHex_roundHex {p : ℝ × ℝ} (hp : p ≠ 0) : unroundHex (roundHex p) = p := by
  have hg := hexGauge_pos hp
  have hn := norm_pos_iff.mpr (planeMap_ne_zero hp)
  unfold unroundHex
  rw [norm_planeMap_roundHex]
  rw [roundHex,hexGauge_smul,abs_of_pos (div_pos hg hn),smul_smul]
  have hcoeff : hexGauge p / (hexGauge p / ‖HexTiling.planeMap p‖ * hexGauge p) *
      (hexGauge p / ‖HexTiling.planeMap p‖) = 1 := by field_simp
  rw [hcoeff,one_smul]

theorem roundHex_unroundHex {p : ℝ × ℝ} (hp : p ≠ 0) : roundHex (unroundHex p) = p := by
  have hg := hexGauge_pos hp
  have hn := norm_pos_iff.mpr (planeMap_ne_zero hp)
  unfold roundHex
  rw [unroundHex,hexGauge_smul,planeMap_smul,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos hn hg),smul_smul]
  have hcoeff : (‖HexTiling.planeMap p‖ / hexGauge p * hexGauge p) /
      (‖HexTiling.planeMap p‖ / hexGauge p * ‖HexTiling.planeMap p‖) *
      (‖HexTiling.planeMap p‖ / hexGauge p) = 1 := by field_simp
  rw [hcoeff,one_smul]

#print axioms norm_planeMap_roundHex
#print axioms unroundHex_roundHex
#print axioms roundHex_unroundHex

/-- Explicit homeomorphism of the punctured plane. Its image of every
hexagonal level set has Euclidean radius equal to that level. -/
noncomputable def roundHexHomeomorph : {p : ℝ × ℝ // p ≠ 0} ≃ₜ {p : ℝ × ℝ // p ≠ 0} where
  toFun p := ⟨roundHex p,roundHex_ne_zero p.property⟩
  invFun p := ⟨unroundHex p,unroundHex_ne_zero p.property⟩
  left_inv p := Subtype.ext (unroundHex_roundHex p.property)
  right_inv p := Subtype.ext (roundHex_unroundHex p.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_hexGauge.comp continuous_subtype_val).div
      (HexTiling.continuous_planeMap.comp continuous_subtype_val).norm
      (fun p => (norm_pos_iff.mpr (planeMap_ne_zero p.property)).ne')).smul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((HexTiling.continuous_planeMap.comp continuous_subtype_val).norm.div
      (continuous_hexGauge.comp continuous_subtype_val)
      (fun p => (hexGauge_pos p.property).ne')).smul continuous_subtype_val

noncomputable def planeInverse (z : ℂ) : ℝ × ℝ :=
  (z.re-z.im/Real.sqrt 3,2*z.im/Real.sqrt 3)

theorem planeMap_planeInverse (z : ℂ) : HexTiling.planeMap (planeInverse z) = z := by
  have hs : Real.sqrt (3:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Complex.ext
  · dsimp [HexTiling.planeMap,planeInverse]
    ring
  · dsimp [HexTiling.planeMap,planeInverse]
    field_simp

theorem planeInverse_planeMap (p : ℝ × ℝ) : planeInverse (HexTiling.planeMap p) = p :=
  HexTiling.planeMap_injective (planeMap_planeInverse _)

noncomputable def planeMapHomeomorph : (ℝ × ℝ) ≃ₜ ℂ where
  toFun := HexTiling.planeMap
  invFun := planeInverse
  left_inv := planeInverse_planeMap
  right_inv := planeMap_planeInverse
  continuous_toFun := HexTiling.continuous_planeMap
  continuous_invFun := by unfold planeInverse; fun_prop

#print axioms roundHexHomeomorph
#print axioms planeMapHomeomorph

theorem hexGauge_unroundHex (p : ℝ × ℝ) :
    hexGauge (unroundHex p) = ‖HexTiling.planeMap p‖ := by
  by_cases hp : p = 0
  · subst p
    simp [unroundHex,hexGauge,planeMap_zero]
  · have hg := hexGauge_pos hp
    have hn := norm_pos_iff.mpr (planeMap_ne_zero hp)
    rw [unroundHex,hexGauge_smul,abs_of_pos (div_pos hn hg)]
    exact div_mul_cancel₀ _ hg.ne'

def hexAnnulus (r R : ℝ) : Set (ℝ × ℝ) := {p | r ≤ hexGauge p ∧ hexGauge p ≤ R}
def roundAnnulus (r R : ℝ) : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}

theorem hexAnnulus_ne_zero {r R : ℝ} (hr : 0 < r) (p : hexAnnulus r R) :
    (p : ℝ × ℝ) ≠ 0 := by
  intro h
  have hp := p.property.1
  rw [h,(hexGauge_eq_zero_iff 0).mpr rfl] at hp
  linarith

theorem roundAnnulus_ne_zero {r R : ℝ} (hr : 0 < r) (z : roundAnnulus r R) : (z : ℂ) ≠ 0 := by
  intro h
  have hz := z.property.1
  rw [h,norm_zero] at hz
  linarith

/-- Exact topological annulus dictionary, proved rather than included in
the crosscut-order input. Both boundary components become literal
Euclidean circles, with their radii unchanged. -/
noncomputable def hexAnnulusHomeomorph (r R : ℝ) (hr : 0 < r) :
    hexAnnulus r R ≃ₜ roundAnnulus r R where
  toFun p := ⟨HexTiling.planeMap (roundHex p),by
    change r ≤ ‖HexTiling.planeMap (roundHex p)‖ ∧ ‖HexTiling.planeMap (roundHex p)‖ ≤ R
    rw [norm_planeMap_roundHex]
    exact p.property⟩
  invFun z := ⟨unroundHex (planeInverse z),by
    change r ≤ hexGauge (unroundHex (planeInverse z)) ∧ hexGauge (unroundHex (planeInverse z)) ≤ R
    rw [hexGauge_unroundHex,planeMap_planeInverse]
    exact z.property⟩
  left_inv p := by
    apply Subtype.ext
    change unroundHex (planeInverse (HexTiling.planeMap (roundHex p))) = p
    rw [planeInverse_planeMap,unroundHex_roundHex (hexAnnulus_ne_zero hr p)]
  right_inv z := by
    apply Subtype.ext
    change HexTiling.planeMap (roundHex (unroundHex (planeInverse z))) = z
    have hz : planeInverse (z:ℂ) ≠ 0 := by
      intro h
      have he := planeMap_planeInverse (z:ℂ)
      rw [h,planeMap_zero] at he
      exact roundAnnulus_ne_zero hr z he.symm
    rw [roundHex_unroundHex hz,planeMap_planeInverse]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply HexTiling.continuous_planeMap.comp
    exact ((continuous_hexGauge.comp continuous_subtype_val).div
      (HexTiling.continuous_planeMap.comp continuous_subtype_val).norm
      (fun p => (norm_pos_iff.mpr (planeMap_ne_zero (hexAnnulus_ne_zero hr p))).ne')).smul
        continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun z : roundAnnulus r R => planeInverse z) :=
      planeMapHomeomorph.symm.continuous.comp continuous_subtype_val
    exact ((HexTiling.continuous_planeMap.comp hc).norm.div
      (continuous_hexGauge.comp hc) (fun z => by
        apply (hexGauge_pos ?_).ne'
        intro h
        dsimp at h
        have he := planeMap_planeInverse (z:ℂ)
        rw [h,planeMap_zero] at he
        exact roundAnnulus_ne_zero hr z he.symm)).smul hc

theorem hexAnnulusHomeomorph_radius (r R : ℝ) (hr : 0 < r) (p : hexAnnulus r R) :
    ‖(hexAnnulusHomeomorph r R hr p : ℂ)‖ = hexGauge p := norm_planeMap_roundHex p

#print axioms hexAnnulusHomeomorph

theorem arg_planeMap_roundHex {p : ℝ × ℝ} (hp : p ≠ 0) :
    Complex.arg (HexTiling.planeMap (roundHex p)) = Complex.arg (HexTiling.planeMap p) := by
  rw [roundHex,planeMap_smul]
  change Complex.arg ((hexGauge p / ‖HexTiling.planeMap p‖ : ℝ) * HexTiling.planeMap p) = _
  exact Complex.arg_real_mul _ (div_pos (hexGauge_pos hp) (norm_pos_iff.mpr (planeMap_ne_zero hp)))

theorem hexAnnulusHomeomorph_arg (r R : ℝ) (hr : 0 < r) (p : hexAnnulus r R) :
    Complex.arg (hexAnnulusHomeomorph r R hr p : ℂ) = Complex.arg (HexTiling.planeMap p) :=
  arg_planeMap_roundHex (hexAnnulus_ne_zero hr p)

#print axioms hexAnnulusHomeomorph_arg

end ExceptionalTimes.Annulus
