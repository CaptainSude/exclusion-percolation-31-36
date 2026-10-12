import ExceptionalTimes.FrostmanEnergy
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Literal occupation measures and their moment identities. These lemmas retain
the extended nonnegative kernel, including its infinite diagonal. They do not
assume existence of occupation-measure witnesses or a correlation estimate.
-/

namespace ExceptionalTimes.OccupationMoments

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]

noncomputable def kernelEnergy (K : T × T → ℝ≥0∞) (ν : Measure T) : ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ t, K (s, t) ∂ν ∂ν

theorem kernelEnergy_withDensity (ν : Measure T) [SFinite ν]
    {f : T → ℝ≥0∞} (hf : Measurable f)
    {K : T × T → ℝ≥0∞} (hK : Measurable K) :
    kernelEnergy K (ν.withDensity f) =
      ∫⁻ s, ∫⁻ t, K (s, t) * f s * f t ∂ν ∂ν := by
  have hi (s : T) : (∫⁻ t, K (s, t) ∂ν.withDensity f) =
      ∫⁻ t, f t * K (s, t) ∂ν := by
    exact lintegral_withDensity_eq_lintegral_mul ν hf (by fun_prop)
  unfold kernelEnergy
  simp_rw [hi]
  rw [lintegral_withDensity_eq_lintegral_mul ν hf (by fun_prop)]
  apply lintegral_congr
  intro s
  change f s * (∫⁻ t, f t * K (s, t) ∂ν) = _
  rw [← lintegral_const_mul _ (by fun_prop : Measurable (fun t => f t * K (s, t)))]
  apply lintegral_congr
  intro t
  ac_rfl

theorem expected_kernelEnergy_withDensity (μ : Measure Ω) [SFinite μ]
    (ν : Measure T) [SFinite ν] {f : Ω → T → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f))
    {K : T × T → ℝ≥0∞} (hK : Measurable K) :
    (∫⁻ ω, kernelEnergy K (ν.withDensity (f ω)) ∂μ) =
      ∫⁻ s, ∫⁻ t, K (s, t) * (∫⁻ ω, f ω s * f ω t ∂μ) ∂ν ∂ν := by
  have hf' (ω : Ω) : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
  simp_rw [kernelEnergy_withDensity ν (hf' _) hK]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro s
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro t
  rw [← lintegral_const_mul _ (by fun_prop : Measurable (fun ω => f ω s * f ω t))]
  apply lintegral_congr
  intro ω
  ac_rfl

/-- Occupation on the base time measure `ν`, normalized by `c`.
For a finite window take `ν = volume.restrict J`, `c = a⁻¹`.
The event is a genuine subset of sample/time pairs. -/
noncomputable def occupation (ν : Measure T) (c : ℝ≥0∞)
    (E : Set (Ω × T)) (ω : Ω) : Measure T :=
  ν.withDensity (fun t => c * (E.indicator (fun _ => 1) (ω, t)))

theorem occupation_density_measurable {E : Set (Ω × T)} (hE : MeasurableSet E)
    (c : ℝ≥0∞) :
    Measurable (fun p : Ω × T => c * E.indicator (fun _ => (1 : ℝ≥0∞)) p) := by
  exact measurable_const.mul (measurable_const.indicator hE)

theorem occupation_eq_smul_restrict (ν : Measure T) (c : ℝ≥0∞)
    {E : Set (Ω × T)} (hE : MeasurableSet E) (ω : Ω) :
    occupation ν c E ω = c • ν.restrict {t | (ω, t) ∈ E} := by
  have hs : MeasurableSet {t | (ω, t) ∈ E} := hE.preimage (by fun_prop)
  have hd : (fun t => c * E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t)) =
      {t | (ω, t) ∈ E}.indicator (fun _ => c) := by
    funext t
    by_cases ht : (ω, t) ∈ E <;> simp [ht]
  rw [occupation, hd, withDensity_indicator hs, withDensity_const]

theorem occupation_concentrated (ν : Measure T) (c : ℝ≥0∞)
    {E : Set (Ω × T)} (hE : MeasurableSet E) (ω : Ω) :
    occupation ν c E ω {t | (ω, t) ∉ E} = 0 := by
  rw [occupation_eq_smul_restrict ν c hE ω]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hs : MeasurableSet {t | (ω, t) ∉ E} :=
    (hE.preimage (by fun_prop : Measurable (fun t => (ω, t)))).compl
  rw [Measure.restrict_apply hs]
  rw [show {t | (ω, t) ∉ E} ∩ {t | (ω, t) ∈ E} = (∅ : Set T) by ext t; simp]
  simp

omit [MeasurableSpace Ω] in
theorem occupation_mass (ν : Measure T) (c : ℝ≥0∞)
    (E : Set (Ω × T)) (ω : Ω) :
    occupation ν c E ω univ =
      ∫⁻ t, c * E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t) ∂ν := by
  simp [occupation, withDensity_apply _ MeasurableSet.univ]

theorem measurable_occupation_mass (ν : Measure T) [SFinite ν] (c : ℝ≥0∞)
    {E : Set (Ω × T)} (hE : MeasurableSet E) :
    Measurable (fun ω => occupation ν c E ω univ) := by
  simp_rw [occupation_mass]
  exact (occupation_density_measurable hE c).lintegral_prod_right

theorem expected_occupation_mass (μ : Measure Ω) [SFinite μ]
    (ν : Measure T) [SFinite ν] (c : ℝ≥0∞)
    {E : Set (Ω × T)} (hE : MeasurableSet E) :
    (∫⁻ ω, occupation ν c E ω univ ∂μ) =
      ∫⁻ t, c * μ {ω | (ω, t) ∈ E} ∂ν := by
  simp_rw [occupation_mass]
  rw [lintegral_lintegral_swap (f := fun ω t => c * E.indicator (fun _ => 1) (ω, t))
    (occupation_density_measurable hE c).aemeasurable]
  apply lintegral_congr
  intro t
  have hs : MeasurableSet {ω | (ω, t) ∈ E} := hE.preimage (by fun_prop)
  change (∫⁻ ω, c * ({ω | (ω, t) ∈ E}.indicator (fun _ => 1) ω) ∂μ) = _
  rw [lintegral_const_mul _ (measurable_const.indicator hs), lintegral_indicator_const hs]
  simp

theorem expected_occupation_energy (μ : Measure Ω) [SFinite μ]
    (ν : Measure T) [SFinite ν] (c : ℝ≥0∞)
    {E : Set (Ω × T)} (hE : MeasurableSet E)
    {K : T × T → ℝ≥0∞} (hK : Measurable K) :
    (∫⁻ ω, kernelEnergy K (occupation ν c E ω) ∂μ) =
      ∫⁻ s, ∫⁻ t, K (s, t) * c ^ 2 *
        μ {ω | (ω, s) ∈ E ∧ (ω, t) ∈ E} ∂ν ∂ν := by
  unfold occupation
  rw [expected_kernelEnergy_withDensity μ ν
    (f := fun ω t => c * E.indicator (fun _ => 1) (ω, t))
    (occupation_density_measurable hE c) hK]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro t
  have hs : MeasurableSet {ω | (ω, s) ∈ E ∧ (ω, t) ∈ E} :=
    (hE.preimage (by fun_prop)).inter (hE.preimage (by fun_prop))
  have heq : (fun ω => (c * E.indicator (fun _ => 1) (ω, s)) *
      (c * E.indicator (fun _ => 1) (ω, t))) =
      (fun ω => c ^ 2 * {ω | (ω, s) ∈ E ∧ (ω, t) ∈ E}.indicator (fun _ => 1) ω) := by
    funext ω
    by_cases hs : (ω, s) ∈ E <;> by_cases ht : (ω, t) ∈ E <;>
      simp [hs, ht, pow_two]
  rw [heq, lintegral_const_mul _ (measurable_const.indicator hs), lintegral_indicator_const hs]
  simp only [one_mul, mul_assoc]

theorem kernelEnergy_one (ν : Measure T) :
    kernelEnergy (fun _ => 1) ν = (ν univ) ^ 2 := by
  simp [kernelEnergy, pow_two]

theorem expected_occupation_mass_sq (μ : Measure Ω) [SFinite μ]
    (ν : Measure T) [SFinite ν] (c : ℝ≥0∞)
    {E : Set (Ω × T)} (hE : MeasurableSet E) :
    (∫⁻ ω, (occupation ν c E ω univ) ^ 2 ∂μ) =
      ∫⁻ s, ∫⁻ t, c ^ 2 *
        μ {ω | (ω, s) ∈ E ∧ (ω, t) ∈ E} ∂ν ∂ν := by
  simpa only [kernelEnergy_one, one_mul] using
    expected_occupation_energy μ ν c hE (K := fun _ => 1) measurable_const

theorem measurable_occupation_energy (ν : Measure T) [SFinite ν] (c : ℝ≥0∞)
    {E : Set (Ω × T)} (hE : MeasurableSet E)
    {K : T × T → ℝ≥0∞} (hK : Measurable K) :
    Measurable (fun ω => kernelEnergy K (occupation ν c E ω)) := by
  have hf := occupation_density_measurable hE c
  have hf' (ω : Ω) : Measurable (fun t => c * E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, t)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  unfold occupation
  simp_rw [kernelEnergy_withDensity ν (hf' _) hK]
  fun_prop

/-- Under a stationary one-time marginal, normalization gives the exact
expected occupation mass. Stationarity is an explicit hypothesis here. -/
theorem expected_normalized_occupation_mass (μ : Measure Ω) [SFinite μ]
    (ν : Measure T) [SFinite ν] {a : ℝ≥0∞} (ha : a ≠ 0) (hatop : a ≠ ⊤)
    {E : Set (Ω × T)} (hE : MeasurableSet E)
    (hmarginal : ∀ t, μ {ω | (ω, t) ∈ E} = a) :
    (∫⁻ ω, occupation ν a⁻¹ E ω univ ∂μ) = ν univ := by
  rw [expected_occupation_mass μ ν a⁻¹ hE]
  simp_rw [hmarginal, ENNReal.inv_mul_cancel ha hatop]
  simp

theorem measurable_frostmanKernel (γ : ℝ) :
    Measurable (fun p : ℝ × ℝ => frostmanKernel γ p.1 p.2) := by
  unfold frostmanKernel
  fun_prop

theorem frostmanEnergy_eq_kernelEnergy (γ : ℝ) (ν : Measure ℝ) :
    frostmanEnergy γ ν = kernelEnergy (fun p => frostmanKernel γ p.1 p.2) ν := rfl

theorem one_le_frostmanKernel_unit {γ s t : ℝ} (hγ : 0 ≤ γ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    1 ≤ frostmanKernel γ s t := by
  have hd : dist s t ≤ 1 := by
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have he : edist s t ≤ 1 := by
    rw [edist_dist]
    simpa using ENNReal.ofReal_le_ofReal hd
  simpa only [frostmanKernel, ENNReal.rpow_zero] using
    ENNReal.rpow_le_rpow_of_exponent_ge he (neg_nonpos.mpr hγ)

/-- On a unit interval the energy already controls squared total mass.
The statement includes measures with atoms or infinite total mass. -/
theorem mass_sq_le_frostmanEnergy_unit {γ : ℝ} (hγ : 0 ≤ γ) (ν : Measure ℝ)
    (hcarry : ν (Icc (0 : ℝ) 1)ᶜ = 0) :
    (ν univ) ^ 2 ≤ frostmanEnergy γ ν := by
  have ha : ∀ᵐ t ∂ν, t ∈ Icc (0 : ℝ) 1 := ae_iff.mpr hcarry
  rw [frostmanEnergy_eq_kernelEnergy, ← kernelEnergy_one]
  unfold kernelEnergy
  apply lintegral_mono_ae
  filter_upwards [ha] with s hs
  apply lintegral_mono_ae
  filter_upwards [ha] with t ht
  exact one_le_frostmanKernel_unit hγ hs ht

theorem expected_occupation_frostmanEnergy (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) [SFinite ν] (c : ℝ≥0∞)
    {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (γ : ℝ) :
    (∫⁻ ω, frostmanEnergy γ (occupation ν c E ω) ∂μ) =
      ∫⁻ s, ∫⁻ t, frostmanKernel γ s t * c ^ 2 *
        μ {ω | (ω, s) ∈ E ∧ (ω, t) ∈ E} ∂ν ∂ν :=
  expected_occupation_energy μ ν c hE (measurable_frostmanKernel γ)

/-- The actual finite-radius connection event used in occupation measures. -/
def oneArmEvent (X : Ω → Trajectory) (v : Site) (R : ℕ) : Set (Ω × ℝ) :=
  {p | OneArm (X p.1 p.2) v R}

theorem measurableSet_oneArmEvent {X : Ω → Trajectory}
    (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2)) (v : Site) (R : ℕ) :
    MeasurableSet (oneArmEvent X v R) :=
  (measurableSet_oneArm v R).preimage hX

/-- Exact moment identity for occupation of the graph-defined one-arm event.
This is an equality, and supplies no estimate on its right-hand side. -/
theorem expected_oneArm_occupation_energy (μ : Measure Ω) [SFinite μ]
    (ν : Measure ℝ) [SFinite ν] (c : ℝ≥0∞) (X : Ω → Trajectory)
    (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2)) (v : Site) (R : ℕ) (γ : ℝ) :
    (∫⁻ ω, frostmanEnergy γ (occupation ν c (oneArmEvent X v R) ω) ∂μ) =
      ∫⁻ s, ∫⁻ t, frostmanKernel γ s t * c ^ 2 *
        μ {ω | OneArm (X ω s) v R ∧ OneArm (X ω t) v R} ∂ν ∂ν :=
  expected_occupation_frostmanEnergy μ ν c (measurableSet_oneArmEvent hX v R) γ

end ExceptionalTimes.OccupationMoments

#print axioms ExceptionalTimes.OccupationMoments.expected_occupation_mass
#print axioms ExceptionalTimes.OccupationMoments.expected_occupation_energy
#print axioms ExceptionalTimes.OccupationMoments.expected_oneArm_occupation_energy
