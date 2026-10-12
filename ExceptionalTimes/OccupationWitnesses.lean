import ExceptionalTimes.PublishedCapacity
import ExceptionalTimes.SecondMoment
import ExceptionalTimes.WindowTimeEnergy

/-!
The checked unit-window occupation-measure argument, from concrete moment
bounds to an almost-sure lower dimension. New percolation energy bounds,
spatial ergodicity and the stochastic site-closure property are explicit;
none is included in the published deterministic capacity input.
-/

namespace ExceptionalTimes.OccupationWitnesses

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
open OccupationMoments PublishedCapacity WindowUpgrade TimeClosure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable positive-probability witness may imply the target only almost
everywhere. Extracting a measurable full-measure subset handles that exception
without assuming measurability of the target predicate. -/
theorem ae_invariant_of_positive_ae_witness (μ : Measure Ω)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) {F : Set Ω}
    (hF : MeasurableSet F) (hp : 0 < μ F) {P : Ω → Prop}
    (hP : ∀ ω, P (e ω) ↔ P ω) (hw : ∀ᵐ ω ∂μ, ω ∈ F → P ω) :
    ∀ᵐ ω ∂μ, P ω := by
  obtain ⟨K, hKae, hKm, hKsub⟩ :=
    Filter.IsMeasurablyGenerated.exists_measurable_subset hw
  have hmeas : μ (F ∩ K) = μ F := by
    apply measure_congr
    filter_upwards [hKae] with ω hω
    simp [hω]
  have hpos : 0 < μ (F ∩ K) := hmeas ▸ hp
  have hs := ae_mem_spatialSaturation μ e he (hF.inter hKm) hpos
  exact hs.mono (fun ω hω => spatialSaturation_subset_of_invariant e hP
    (fun η hη => hKsub hη.2 hη.1) hω)

theorem occupation_witnesses_uniform_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (v : Site) (c : ℕ → ℝ≥0∞) (γ : ℝ) {B : ℝ} (hB : 0 < B)
    (hmean : ∀ R, (∫⁻ ω, unitOccupation X v c R ω univ ∂μ) = 1)
    (hsecond : ∀ R, (∫⁻ ω, (unitOccupation X v c R ω univ) ^ 2 ∂μ) ≤ ENNReal.ofReal B)
    (henergy : ∀ R, (∫⁻ ω, frostmanEnergy γ (unitOccupation X v c R ω) ∂μ) ≤ ENNReal.ofReal B)
    (R : ℕ) :
    ENNReal.ofReal (1 / (8 * B)) ≤ μ (occupationSuccess X v c γ (8 * B ^ 2 + 2) R) := by
  exact SecondMoment.capacity_witness_probability μ
    (measurable_occupation_mass _ _ (measurableSet_oneArmEvent hX v R))
    (measurable_occupation_energy _ _ (measurableSet_oneArmEvent hX v R)
      (measurable_frostmanKernel γ)) (hmean R) hB (hsecond R) (henergy R)

/-- Complete unit-window lower-dimension implication. The moments are for
literal occupation measures of the concrete graph connection event. -/
theorem ae_unit_lowerDimension_of_moments (hcapacity : SchrammSteifCapacity)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (v : Site) (c : ℕ → ℝ≥0∞) (hc : ∀ R, c R ≠ ⊤)
    {γ B : ℝ} (hγ : 0 < γ) (hB : 0 < B)
    (hmean : ∀ R, (∫⁻ ω, unitOccupation X v c R ω univ ∂μ) = 1)
    (hsecond : ∀ R, (∫⁻ ω, (unitOccupation X v c R ω univ) ^ 2 ∂μ) ≤ ENNReal.ofReal B)
    (henergy : ∀ R, (∫⁻ ω, frostmanEnergy γ (unitOccupation X v c R ω) ∂μ) ≤ ENNReal.ofReal B)
    (hpreserve : ∀ᵐ ω ∂μ, SiteClosurePreservesPercolationAt (X ω) v)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
    (hshift : Function.Semiconj X e (translateTrajectory z)) :
    ∀ᵐ ω ∂μ, ENNReal.ofReal γ ≤ dimH (exceptionalTimes (X ω) ∩ Icc 0 1) := by
  let C : ℝ := 8 * B ^ 2 + 2
  let F := occupationSuccess X v c γ C
  have hFm : ∀ R, MeasurableSet (F R) := fun R =>
    measurableSet_occupationSuccess X hX v c γ C R
  have hp : 0 < μ (witnessLimsup F) := by
    have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (8 * B)) := by positivity
    exact hδ.trans_le (le_measure_witnessLimsup μ hFm
      (occupation_witnesses_uniform_probability μ X hX v c γ hB hmean hsecond henergy))
  apply ae_invariant_of_positive_ae_witness μ e he (measurableSet_witnessLimsup hFm) hp
  · intro ω
    rw [hshift ω, exceptionalTimes_translate]
  · filter_upwards [hpreserve] with ω hω
    intro hFω
    exact dimension_of_occupation_limsup hcapacity X hX v c hc hγ
      (by dsimp [C]; positivity) ω hω hFω

/-- Since the unit-interval energy controls squared mass, no separate
second-moment input is needed in the final occupation-measure implication. -/
theorem ae_unit_lowerDimension_of_mean_energy (hcapacity : SchrammSteifCapacity)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (v : Site) (c : ℕ → ℝ≥0∞) (hc : ∀ R, c R ≠ ⊤)
    {γ B : ℝ} (hγ : 0 < γ) (hB : 0 < B)
    (hmean : ∀ R, (∫⁻ ω, unitOccupation X v c R ω univ ∂μ) = 1)
    (henergy : ∀ R, (∫⁻ ω, frostmanEnergy γ (unitOccupation X v c R ω) ∂μ) ≤ ENNReal.ofReal B)
    (hpreserve : ∀ᵐ ω ∂μ, SiteClosurePreservesPercolationAt (X ω) v)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
    (hshift : Function.Semiconj X e (translateTrajectory z)) :
    ∀ᵐ ω ∂μ, ENNReal.ofReal γ ≤ dimH (exceptionalTimes (X ω) ∩ Icc 0 1) := by
  apply ae_unit_lowerDimension_of_moments hcapacity μ X hX v c hc hγ hB hmean
    _ henergy hpreserve e he z hshift
  intro R
  apply le_trans _ (henergy R)
  apply lintegral_mono
  intro ω
  apply mass_sq_le_frostmanEnergy_unit hγ.le
  apply bot_unique
  exact (measure_mono (compl_subset_compl.mpr (closedArmTimeSet_subset (X ω) v R))).trans_eq
    (unitOccupation_carried X hX v c R ω)

/-- Actual normalized two-time connection bounds suffice. This theorem leaves
the new probability estimate on display, instead of replacing it by an
occupation-witness assumption. The stationarity marginal is also explicit. -/
theorem ae_unit_lowerDimension_of_twoTime_bound (hcapacity : SchrammSteifCapacity)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (v : Site) (a : ℕ → ℝ≥0∞) (ha : ∀ R, a R ≠ 0) (hatop : ∀ R, a R ≠ ⊤)
    (hmarginal : ∀ R t, μ {ω | OneArm (X ω t) v R} = a R)
    {γ B : ℝ} (hγ : 0 < γ) (hB : 0 < B)
    (hbound : ∀ R, (∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ t in Icc (0 : ℝ) 1,
      frostmanKernel γ s t * (a R)⁻¹ ^ 2 *
        μ {ω | OneArm (X ω s) v R ∧ OneArm (X ω t) v R}) ≤ ENNReal.ofReal B)
    (hpreserve : ∀ᵐ ω ∂μ, SiteClosurePreservesPercolationAt (X ω) v)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
    (hshift : Function.Semiconj X e (translateTrajectory z)) :
    ∀ᵐ ω ∂μ, ENNReal.ofReal γ ≤ dimH (exceptionalTimes (X ω) ∩ Icc 0 1) := by
  apply ae_unit_lowerDimension_of_mean_energy hcapacity μ X hX v (fun R => (a R)⁻¹)
    (fun R => ENNReal.inv_ne_top.mpr (ha R)) hγ hB _ _ hpreserve e he z hshift
  · intro R
    have hm := expected_normalized_occupation_mass μ (volume.restrict (Icc (0 : ℝ) 1))
      (ha R) (hatop R) (measurableSet_oneArmEvent hX v R) (hmarginal R)
    simpa only [unitOccupation, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
      sub_zero, ENNReal.ofReal_one] using hm
  · intro R
    exact (expected_oneArm_occupation_energy μ (volume.restrict (Icc (0 : ℝ) 1))
      (a R)⁻¹ X hX v R γ).trans_le (hbound R)

/-- A uniform stationary time-lag energy bound gives the actual almost-sure
unit-window dimension lower bound. This connects the energy-transfer modules
to capacity; the time-lag estimate is still the central new obligation. -/
theorem ae_unit_lowerDimension_of_lag_bound (hcapacity : SchrammSteifCapacity)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (v : Site) (a : ℕ → ℝ≥0∞) (ha : ∀ R, a R ≠ 0) (hatop : ∀ R, a R ≠ ⊤)
    (hmarginal : ∀ R t, μ {ω | OneArm (X ω t) v R} = a R)
    (hstationary : ∀ R, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      μ {ω | OneArm (X ω s) v R ∧ OneArm (X ω t) v R} =
        μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω (dist s t)) v R})
    {γ B : ℝ} (hγ : 0 < γ) (hB : 0 < B)
    (hbound : ∀ R, (∫⁻ u in Ioc (0 : ℝ) 1,
      frostmanKernel γ 0 u * (a R)⁻¹ ^ 2 *
        μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω u) v R}) ≤ ENNReal.ofReal B)
    (hpreserve : ∀ᵐ ω ∂μ, SiteClosurePreservesPercolationAt (X ω) v)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (z : Site)
    (hshift : Function.Semiconj X e (translateTrajectory z)) :
    ∀ᵐ ω ∂μ, ENNReal.ofReal γ ≤ dimH (exceptionalTimes (X ω) ∩ Icc 0 1) := by
  apply ae_unit_lowerDimension_of_twoTime_bound hcapacity μ X hX v a ha hatop hmarginal
    hγ (B := 2 * B) (by positivity) _ hpreserve e he z hshift
  intro R
  apply (WindowTimeEnergy.twoTime_energy_le_lag_energy
    (fun u => μ {ω | OneArm (X ω 0) v R ∧ OneArm (X ω u) v R})
    (fun s t => μ {ω | OneArm (X ω s) v R ∧ OneArm (X ω t) v R})
    (hstationary R) γ (a R)⁻¹).trans
  have h := mul_le_mul' (le_refl (2 : ℝ≥0∞)) (hbound R)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using h

end ExceptionalTimes.OccupationWitnesses

#print axioms ExceptionalTimes.OccupationWitnesses.ae_unit_lowerDimension_of_moments
#print axioms ExceptionalTimes.OccupationWitnesses.ae_unit_lowerDimension_of_twoTime_bound
#print axioms ExceptionalTimes.OccupationWitnesses.ae_unit_lowerDimension_of_lag_bound

