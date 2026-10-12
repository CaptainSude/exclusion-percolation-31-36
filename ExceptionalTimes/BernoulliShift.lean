import ExceptionalTimes.ProductSpatialShift
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-! Direct cylinder proof of ergodicity for an arbitrary iid alphabet.
No standard-Borel or Lebesgue-space hypothesis is needed. -/

open MeasureTheory ProbabilityTheory Set Function
open scoped Classical symmDiff

namespace ExceptionalTimes.ProductSpatialShift

variable {B : Type*} [MeasurableSpace B]

instance (ν : Measure B) [IsProbabilityMeasure ν] : IsProbabilityMeasure (columnLaw ν) := by
  unfold columnLaw
  infer_instance

theorem measurePreserving_shift (ν : Measure B) [IsProbabilityMeasure ν] :
    MeasurePreserving (shift (B := B)) (columnLaw ν) (columnLaw ν) where
  measurable := shift.measurable
  map_eq := Measure.infinitePi_map_piCongrLeft (fun _ : ℤ => ν) (Equiv.addRight 1)

theorem shift_iterate_apply (n : ℕ) (ω : ℤ → B) (i : ℤ) :
    (shift (B := B))^[n] ω i = ω (i-(n : ℤ)) := by
  induction n generalizing ω i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply,ih,shift_apply]
      congr 1
      omega

theorem exists_disjoint_shift (S : Finset ℤ) :
    ∃ n : ℕ, Disjoint S (S.image (fun i => i-(n : ℤ))) := by
  let m := S.sup Int.natAbs
  refine ⟨2*m+1,Finset.disjoint_left.mpr ?_⟩
  intro i hi hj
  obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hj
  have hiabs : i.natAbs ≤ m := Finset.le_sup hi
  have hjabs : j.natAbs ≤ m := Finset.le_sup hj
  have hilower : -(i.natAbs : ℤ) ≤ i := by
    have H : -i ≤ ((-i).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at H
    omega
  have hjupper : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  omega

theorem cylinder_shift_independent (ν : Measure B) [IsProbabilityMeasure ν]
    (S : Finset ℤ) (U : Set (S → B)) (hU : MeasurableSet U)
    (n : ℕ) (hdisj : Disjoint S (S.image (fun i => i-(n : ℤ)))) :
    columnLaw ν (cylinder S U ∩ (shift (B := B))^[n] ⁻¹' cylinder S U) =
      columnLaw ν (cylinder S U) ^ 2 := by
  let T := S.image (fun i => i-(n : ℤ))
  let back : (T → B) → (S → B) := fun x i =>
    x ⟨i.val-(n : ℤ),Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  have hback : Measurable back := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  have hindep : iIndepFun (fun i (ω : ℤ → B) => ω i) (columnLaw ν) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have H := (hindep.indepFun_finset S T hdisj (fun i => measurable_pi_apply i)).comp
    measurable_id hback
  have heq : (fun ω : ℤ → B => back (fun i : T => ω i)) =
      fun ω => S.restrict ((shift (B := B))^[n] ω) := by
    funext ω i
    exact (shift_iterate_apply n ω i.val).symm
  have H' := H.measure_inter_preimage_eq_mul U U hU hU
  simp only [Function.comp_def] at H'
  rw [heq] at H'
  change columnLaw ν (cylinder S U ∩ (shift (B := B))^[n] ⁻¹' cylinder S U) =
    columnLaw ν (cylinder S U) *
      columnLaw ν ((shift (B := B))^[n] ⁻¹' cylinder S U) at H'
  rw [((measurePreserving_shift ν).iterate n).measure_preimage hU.cylinder.nullMeasurableSet]
    at H'
  simpa only [pow_two] using H'

theorem exists_cylinder_approx (ν : Measure B) [IsProbabilityMeasure ν]
    {A : Set (ℤ → B)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C ∈ measurableCylinders (fun _ : ℤ => B),
      (columnLaw ν).real (C ∆ A) < ε := by
  have hcover : ∃ D : Set (Set (ℤ → B)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℤ => B) ∧ (columnLaw ν) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ},Set.countable_singleton _,?_,by simp⟩
    simpa only [Set.singleton_subset_iff] using univ_mem_measurableCylinders (fun _ : ℤ => B)
  obtain ⟨C,hC,hlt⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_measurableCylinders hcover generateFrom_measurableCylinders.symm hA
    (ENNReal.ofReal_pos.mpr hε)
  refine ⟨C,hC,?_⟩
  have H := (ENNReal.toReal_lt_toReal (measure_ne_top (columnLaw ν) (C ∆ A))
    ENNReal.ofReal_ne_top).mpr hlt
  simpa only [Measure.real,ENNReal.toReal_ofReal hε.le] using H

theorem invariant_measureReal_idempotent (ν : Measure B) [IsProbabilityMeasure ν]
    {A : Set (ℤ → B)} (hA : MeasurableSet A) (hinv : shift ⁻¹' A = A) :
    (columnLaw ν).real A = ((columnLaw ν).real A)^2 := by
  let μ := columnLaw ν
  have ha0 : 0 ≤ μ.real A := measureReal_nonneg
  have ha1 : μ.real A ≤ 1 := measureReal_le_one
  apply le_antisymm
  · by_contra h
    have hgap : 0 < μ.real A - (μ.real A)^2 := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨C,hC,hδ⟩ := exists_cylinder_approx ν hA (show 0 <
      (μ.real A-(μ.real A)^2)/8 by positivity)
    obtain ⟨S,U,hU,rfl⟩ := (mem_measurableCylinders C).mp hC
    obtain ⟨n,hn⟩ := exists_disjoint_shift S
    let C : Set (ℤ → B) := cylinder S U
    let D := (shift (B := B))^[n] ⁻¹' C
    let δ := μ.real (C ∆ A)
    have hCm : MeasurableSet C := hU.cylinder
    have hDm : MeasurableSet D := hCm.preimage (shift.measurable.iterate n)
    have hin : (shift (B := B))^[n] ⁻¹' A = A := IsFixedPt.preimage_iterate hinv n
    have hDA : μ.real (D ∆ A) = δ := by
      change μ.real (((shift (B := B))^[n] ⁻¹' C) ∆ A) = μ.real (C ∆ A)
      conv_lhs => rw [← hin,← Set.preimage_symmDiff]
      exact ((measurePreserving_shift ν).iterate n).measureReal_preimage
        (hCm.symmDiff hA).nullMeasurableSet
    have hsub : A ∆ (C ∩ D) ⊆ (A ∆ C) ∪ (A ∆ D) := by
      intro ω hω
      simp only [Set.mem_symmDiff,Set.mem_inter_iff,Set.mem_union] at *
      tauto
    have hdiff : μ.real (A ∆ (C ∩ D)) ≤ 2*δ := calc
      _ ≤ μ.real ((A ∆ C) ∪ (A ∆ D)) := measureReal_mono hsub
      _ ≤ μ.real (A ∆ C) + μ.real (A ∆ D) := measureReal_union_le _ _
      _ = _ := by rw [symmDiff_comm A C,symmDiff_comm A D,hDA]; ring
    have hCA := MeasuredSets.real_sub_real_le_dist
      (μ := μ) (⟨C,hCm⟩ : MeasuredSets μ) ⟨A,hA⟩
    change μ.real C - μ.real A ≤ δ at hCA
    have hAI := MeasuredSets.real_sub_real_le_dist
      (μ := μ) (⟨A,hA⟩ : MeasuredSets μ) ⟨C ∩ D,hCm.inter hDm⟩
    change μ.real A - μ.real (C ∩ D) ≤ μ.real (A ∆ (C ∩ D)) at hAI
    have hind : μ.real (C ∩ D) = (μ.real C)^2 := by
      exact congrArg ENNReal.toReal (cylinder_shift_independent ν S U hU n hn)
        |>.trans (ENNReal.toReal_pow _ _)
    have hc0 : 0 ≤ μ.real C := measureReal_nonneg
    have hc1 : μ.real C ≤ 1 := measureReal_le_one
    have hδ0 : 0 ≤ δ := measureReal_nonneg
    have hsquare : (μ.real C)^2 - (μ.real A)^2 ≤ 2*δ := by
      nlinarith [mul_nonneg (show 0 ≤ μ.real C + μ.real A by positivity)
        (sub_nonneg.mpr hCA),mul_nonneg hδ0
          (show 0 ≤ 2-μ.real C-μ.real A by linarith)]
    rw [hind] at hAI
    change δ < (μ.real A-(μ.real A)^2)/8 at hδ
    nlinarith
  · nlinarith

theorem ergodic_shift (ν : Measure B) [IsProbabilityMeasure ν] :
    Ergodic (shift (B := B)) (columnLaw ν) where
  toMeasurePreserving := measurePreserving_shift ν
  aeconst_set := by
    intro A hA hinv
    have H := invariant_measureReal_idempotent ν hA hinv
    have h01 : (columnLaw ν).real A = 0 ∨ (columnLaw ν).real A = 1 := by
      rcases mul_eq_zero.mp (show (columnLaw ν).real A * ((columnLaw ν).real A-1) = 0
        by nlinarith [H]) with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rw [Filter.eventuallyEmptyOrUniv_iff']
    rcases h01 with h0 | h1
    · exact Or.inl (ae_eq_empty.mpr ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp h0))
    · apply Or.inr
      apply ae_eq_univ.mpr
      rw [measure_compl hA (measure_ne_top _ _)]
      have hμ : columnLaw ν A = 1 := by
        apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
        simpa only [Measure.real,ENNReal.toReal_one] using h1
      simp [hμ]

#print axioms ergodic_shift

theorem ergodic_translation (ν : Measure B) [IsProbabilityMeasure ν] :
    Ergodic (translation (B := B) (1,0)) (latticeLaw ν) :=
  ergodic_translation_of_columnShift ν (ergodic_shift (columnLaw ν))

#print axioms ergodic_translation

end ExceptionalTimes.ProductSpatialShift
