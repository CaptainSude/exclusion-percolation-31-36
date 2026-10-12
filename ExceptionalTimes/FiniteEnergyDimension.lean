import ExceptionalTimes.LagScaling
import ExceptionalTimes.ClockTruncationAE
import ExceptionalTimes.FairOneArm

/-! The finite-edge route into the complete all-window dimension reduction.
The finite energy estimate and actual process properties remain displayed
obligations. This file does not classify them as published results. -/

namespace ExceptionalTimes.FiniteEnergyDimension

open MeasureTheory Set Filter
open scoped ENNReal

theorem normalized_energy_le {T : Type*} [MeasurableSpace T] (ν : Measure T)
    (w q : T → ℝ≥0∞) {α C : ℝ≥0∞} (hα : α ≠ 0) (hαtop : α ≠ ⊤)
    (hbound : (∫⁻ t, w t * q t ∂ν) ≤ C * α ^ 2) :
    (∫⁻ t, w t * α⁻¹ ^ 2 * q t ∂ν) ≤ C := by
  have hinv : α⁻¹ ^ 2 ≠ ⊤ := by simp [hα]
  have heq : (∫⁻ t, w t * α⁻¹ ^ 2 * q t ∂ν) =
      α⁻¹ ^ 2 * ∫⁻ t, w t * q t ∂ν := by
    calc
      _ = ∫⁻ t, α⁻¹ ^ 2 * (w t * q t) ∂ν := by
        apply lintegral_congr
        intro t
        ac_rfl
      _ = _ := lintegral_const_mul' _ _ hinv
  rw [heq]
  apply (mul_le_mul' le_rfl hbound).trans_eq
  calc
    α⁻¹ ^ 2 * (C * α ^ 2) = C * (α⁻¹ * α) ^ 2 := by rw [mul_pow]; ac_rfl
    _ = C := by rw [ENNReal.inv_mul_cancel hα hαtop, one_pow, mul_one]

theorem almostSureConjecturedDimension_of_finite_energy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (hX : Measurable (fun p : Ω × ℝ => P.trajectories p.1 p.2))
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (v : Site) (hv : ∀ R, v ∈ latticeBox R)
    (α : ℕ → ℝ≥0∞) (hα : ∀ R, α R ≠ 0) (hαtop : ∀ R, α R ≠ ⊤)
    (hmarginal : ∀ R t, μ {ω | OneArm (P.trajectories ω t) v R} = α R)
    (hstationary : ∀ R s t, 0 ≤ s → 0 ≤ t →
      μ {ω | OneArm (P.trajectories ω s) v R ∧ OneArm (P.trajectories ω t) v R} =
        μ {ω | OneArm (P.trajectories ω 0) v R ∧
          OneArm (P.trajectories ω (dist s t)) v R})
    (htrunc : ∀ n t, AEMeasurable (fun ω => P.truncatedTrajectories (F n) ω t) μ)
    (htime : ∀ n R γ, AEMeasurable
      (fun t => frostmanKernel γ 0 t *
        P.truncatedPairedCylinderProbability (F n) (fun η => OneArm η v R) t)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hfinite : ∀ γ : ℝ, 0 < γ → γ < 31 / 36 → ∃ B : ℝ, 0 < B ∧ ∀ R, ∀ᶠ n in atTop,
      P.truncatedCorrelationEnergy (F n) (fun η => OneArm η v R) γ
        (volume.restrict (Ioc (0 : ℝ) 1)) ≤ ENNReal.ofReal B * (α R) ^ 2)
    (hpreserve : ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (P.trajectories ω) v)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
    (hshift : Function.Semiconj P.trajectories e (translateTrajectory z))
    (hupper : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (P.trajectories ω)) ≤ (31 / 36 : ℝ≥0∞)) :
    AlmostSureConjecturedDimension μ P.trajectories := by
  let : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  apply LagScaling.almostSureConjecturedDimension_of_lag_energy hcapacity μ
    P.trajectories hX v α hα hαtop hmarginal hstationary ?_ hpreserve e he z hshift hupper
  intro γ hγ hγd
  obtain ⟨B, hB, hbound⟩ := hfinite γ hγ hγd
  refine ⟨B, hB, ?_⟩
  intro R
  have hfull : ∀ t, Measurable (fun ω => P.trajectories ω t) :=
    fun t => hX.comp (measurable_id.prodMk measurable_const)
  have hb := P.oneArm_correlationEnergy_le_of_truncated_bound_ae F hmono hex v R (hv R)
    (fun t => (hfull t).aemeasurable) htrunc γ (volume.restrict (Ioc (0 : ℝ) 1))
    (fun n => htime n R γ) (ENNReal.ofReal B * (α R) ^ 2) (hbound R)
  have hn := normalized_energy_le (volume.restrict (Ioc (0 : ℝ) 1))
    (frostmanKernel γ 0) (P.pairedCylinderProbability (fun η => OneArm η v R))
    (hα R) (hαtop R) hb
  simpa only [PoissonGraphicalRealization.pairedCylinderProbability, P.trajectories_zero] using hn

end ExceptionalTimes.FiniteEnergyDimension

#print axioms ExceptionalTimes.FiniteEnergyDimension.almostSureConjecturedDimension_of_finite_energy

