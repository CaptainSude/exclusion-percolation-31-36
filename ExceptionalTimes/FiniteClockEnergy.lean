import ExceptionalTimes.FiniteClockGridLaw

/-! Exact actual finite-clock correlations and the proved spectral energy
comparison. No representation or CTMC input is assumed. -/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace ExceptionalTimes.FiniteClockEnergy

open FiniteClockBridge FiniteClockGridLaw FiniteGenerator FiniteFractional FiniteSpectralEnergy

variable {Ξ I : Type*} [MeasurableSpace Ξ] [Fintype I] [DecidableEq I]
variable {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
variable (V : Finset Site) (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
variable (hinj : Function.Injective (edgePair V edge))
variable (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
include hinj hr

theorem truncated_cylinder_correlation (t : ℝ) (ht : 0 < t) (E : (V → Bool) → Prop) :
    P.truncatedPairedCylinderProbability (retainedEdges V edge) (fun η => E (restrictColor V η)) t =
      ENNReal.ofReal (correlation
        (complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
          (fun i => rate (edgePair V edge i))) (FiniteClockLaw.indicatorVector E) t) :=
  projected_paired_correlation V P edge hinj hr t ht E

theorem truncated_energy_eq_shortEnergy (E : (V → Bool) → Prop) {γ : ℝ} (hγ : γ < 1) :
    P.truncatedCorrelationEnergy (retainedEdges V edge) (fun η => E (restrictColor V η)) γ
      (volume.restrict (Ioc (0 : ℝ) 1)) =
      ENNReal.ofReal (shortEnergy
        (complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
          (fun i => rate (edgePair V edge i))) (FiniteClockLaw.indicatorVector E) (1 - γ)) := by
  unfold PoissonGraphicalRealization.truncatedCorrelationEnergy
  calc
    _ = ∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t * ENNReal.ofReal (correlation
        (complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
          (fun i => rate (edgePair V edge i))) (FiniteClockLaw.indicatorVector E) t) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      rw [truncated_cylinder_correlation V P edge hinj hr t ht.1 E]
    _ = _ := frostman_lintegral_eq_shortEnergy
      (Matrix.nonneg_iff_posSemidef.mp (complexGenerator_nonneg _
        (fun _ => colorSwap_involutive _ _) _ hr)) _ hγ

theorem truncated_energy_le_comparator
    (A : Matrix (V → Bool) (V → Bool) ℂ) (hA : A.PosSemidef)
    (hAB : A ≤ complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
      (fun i => rate (edgePair V edge i)))
    (E : (V → Bool) → Prop) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    P.truncatedCorrelationEnergy (retainedEdges V edge) (fun η => E (restrictColor V η)) γ
      (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (Real.exp 1 + 1) *
        ∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t *
          ENNReal.ofReal (correlation A (FiniteClockLaw.indicatorVector E) t) := by
  unfold PoissonGraphicalRealization.truncatedCorrelationEnergy
  calc
    _ = ∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t * ENNReal.ofReal (correlation
        (complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
          (fun i => rate (edgePair V edge i))) (FiniteClockLaw.indicatorVector E) t) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      rw [truncated_cylinder_correlation V P edge hinj hr t ht.1 E]
    _ ≤ _ := frostman_lintegral_comparison hA
      (Matrix.nonneg_iff_posSemidef.mp (complexGenerator_nonneg _
        (fun _ => colorSwap_involutive _ _) _ hr)) hAB _ hγ0 hγ1

theorem truncated_time_aemeasurable (E : (V → Bool) → Prop) (γ : ℝ) :
    AEMeasurable (fun t => frostmanKernel γ 0 t *
      P.truncatedPairedCylinderProbability (retainedEdges V edge)
        (fun η => E (restrictColor V η)) t) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hA := Matrix.nonneg_iff_posSemidef.mp (complexGenerator_nonneg
    (fun i => colorSwap (edge i).1 (edge i).2) (fun _ => colorSwap_involutive _ _)
      (fun i => rate (edgePair V edge i)) hr)
  have hm : Measurable (fun t => frostmanKernel γ 0 t * ENNReal.ofReal (correlation
      (complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
        (fun i => rate (edgePair V edge i))) (FiniteClockLaw.indicatorVector E) t)) := by
    apply Measurable.mul
    · unfold frostmanKernel
      fun_prop
    · exact ENNReal.measurable_ofReal.comp (measurable_correlation hA.isHermitian _)
  apply hm.aemeasurable.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  rw [truncated_cylinder_correlation V P edge hinj hr t ht.1 E]

#print axioms truncated_cylinder_correlation
#print axioms truncated_energy_eq_shortEnergy
#print axioms truncated_energy_le_comparator
#print axioms truncated_time_aemeasurable

end ExceptionalTimes.FiniteClockEnergy
