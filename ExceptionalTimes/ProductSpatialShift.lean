import ExceptionalTimes.ClockSpatial
import Mathlib.Probability.ProductMeasure
import Mathlib.Dynamics.Ergodic.Ergodic

/-! The exact dictionary between an iid lattice product and the two-sided
shift of its vertical columns. No ergodicity theorem is assumed here:
the last lemma transports an explicitly supplied column-shift theorem. -/

open MeasureTheory Function

namespace ExceptionalTimes.ProductSpatialShift

variable {B : Type*} [MeasurableSpace B]

noncomputable def latticeLaw (ν : Measure B) : Measure (Site → B) :=
  Measure.infinitePi (fun _ => ν)

noncomputable def columnLaw (ν : Measure B) : Measure (ℤ → B) :=
  Measure.infinitePi (fun _ => ν)

noncomputable def columnsLaw (ν : Measure B) : Measure (ℤ → ℤ → B) :=
  Measure.infinitePi (fun _ => columnLaw ν)

def translation (z : Site) : (Site → B) ≃ᵐ (Site → B) :=
  MeasurableEquiv.piCongrLeft (fun _ => B) (Equiv.addRight z)

theorem translation_apply (z : Site) (ω : Site → B) (v : Site) :
    translation z ω v = ω (v-z) := by
  simp [translation,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,sub_eq_add_neg]

def columns : (Site → B) ≃ᵐ (ℤ → ℤ → B) := MeasurableEquiv.curry ℤ ℤ B

def shift : (ℤ → B) ≃ᵐ (ℤ → B) :=
  MeasurableEquiv.piCongrLeft (fun _ => B) (Equiv.addRight (1 : ℤ))

theorem shift_apply (ω : ℤ → B) (x : ℤ) : shift ω x = ω (x-1) := by
  simp [shift,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,sub_eq_add_neg]

theorem measurePreserving_translation (ν : Measure B) [IsProbabilityMeasure ν] (z : Site) :
    MeasurePreserving (translation z) (latticeLaw ν) (latticeLaw ν) where
  measurable := (translation z).measurable
  map_eq := Measure.infinitePi_map_piCongrLeft (fun _ : Site => ν) (Equiv.addRight z)

theorem measurePreserving_columns (ν : Measure B) [IsProbabilityMeasure ν] :
    MeasurePreserving (columns (B := B)) (latticeLaw ν) (columnsLaw ν) where
  measurable := columns.measurable
  map_eq := Measure.infinitePi_map_curry (fun _ _ : ℤ => ν)

theorem columns_semiconj :
    Semiconj (columns (B := B)) (translation (1,0)) (shift (B := ℤ → B)) := by
  intro ω
  funext x y
  change translation (1,0) ω (x,y) = shift (columns ω) x y
  rw [translation_apply,shift_apply]
  change ω (x-1,y-0) = ω (x-1,y)
  rw [sub_zero]

theorem columns_symm_semiconj :
    Semiconj (columns (B := B)).symm (shift (B := ℤ → B)) (translation (1,0)) := by
  intro ω
  apply columns.injective
  rw [MeasurableEquiv.apply_symm_apply,columns_semiconj,MeasurableEquiv.apply_symm_apply]

theorem ergodic_translation_of_columnShift (ν : Measure B) [IsProbabilityMeasure ν]
    (h : Ergodic (shift (B := ℤ → B)) (columnsLaw ν)) :
    Ergodic (translation (B := B) (1,0)) (latticeLaw ν) :=
  ((measurePreserving_columns ν).symm columns).ergodic_of_ergodic_semiconj h
    (translation (1,0)).measurable columns_symm_semiconj

#print axioms measurePreserving_translation
#print axioms ergodic_translation_of_columnShift

end ExceptionalTimes.ProductSpatialShift
