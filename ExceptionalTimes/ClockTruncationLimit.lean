import ExceptionalTimes.ClockTruncation
import ExceptionalTimes.FrostmanEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Cylinder probabilities and nonnegative energies under clock truncation

All approximations use the literal finite-edge clock restriction and the
transported trajectories from `ClockTruncation`. Pathwise eventual equality
gives bounded-test expectation convergence by dominated convergence. Fatou
then transfers uniform nonnegative weighted correlation bounds. Measurability
of the relevant random variables and time kernels is explicitly required;
no semigroup identification or graphical construction theorem is assumed.

The energy kernel is the extended-valued Frostman kernel. Its positive-exponent
diagonal remains infinity, rather than being reset to zero.
-/

namespace ExceptionalTimes

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PoissonGraphicalRealization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

noncomputable def truncatedTrajectories (P : PoissonGraphicalRealization μ rate)
    (F : Finset (Sym2 Site)) : Ω → Trajectory := fun ω =>
  ((P.clocks ω).restrictEdges F).trajectory
    (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts ω) F) (P.initial ω)

/-- Actual bounded nonnegative two-time tests converge in expectation. The
bound is finite and uniform in both input configurations. -/
theorem tendsto_lintegral_truncated_test (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (t : ℝ) (A : Finset Site) (test : Configuration → Configuration → ℝ≥0∞)
    (hlocal : ∀ initial η ξ, (∀ v ∈ A, η v = ξ v) → test initial η = test initial ξ)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hbound : ∀ initial η, test initial η ≤ B)
    (hmeas : ∀ n, Measurable (fun ω => test (P.initial ω) (P.truncatedTrajectories (F n) ω t))) :
    Tendsto (fun n => ∫⁻ ω, test (P.initial ω) (P.truncatedTrajectories (F n) ω t) ∂μ)
      atTop (𝓝 (∫⁻ ω, test (P.initial ω) (P.trajectories ω t) ∂μ)) := by
  let : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  apply tendsto_lintegral_of_dominated_convergence (fun _ => B) hmeas
  · intro n
    exact ae_of_all μ (fun ω => hbound _ _)
  · simpa using hB
  · apply ae_of_all μ
    intro ω
    obtain ⟨N, hN⟩ := P.eventually_truncated_two_time_test_eq F hmono hex t A test hlocal ω
    exact tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => hN n hn)

noncomputable def pairedCylinderProbability (P : PoissonGraphicalRealization μ rate)
    (E : Configuration → Prop) (t : ℝ) : ℝ≥0∞ :=
  μ {ω | E (P.initial ω) ∧ E (P.trajectories ω t)}

noncomputable def truncatedPairedCylinderProbability (P : PoissonGraphicalRealization μ rate)
    (F : Finset (Sym2 Site)) (E : Configuration → Prop) (t : ℝ) : ℝ≥0∞ :=
  μ {ω | E (P.initial ω) ∧ E (P.truncatedTrajectories F ω t)}

/-- Paired events are measured on the supplied graphical probability space,
with the identical initial field and the actual truncated clock trajectories. -/
theorem tendsto_pairedCylinderProbability (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (t : ℝ) (A : Finset Site) (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ v ∈ A, η v = ξ v) → (E η ↔ E ξ))
    (hfull : MeasurableSet {ω | E (P.initial ω) ∧ E (P.trajectories ω t)})
    (hmeas : ∀ n, MeasurableSet {ω | E (P.initial ω) ∧ E (P.truncatedTrajectories (F n) ω t)}) :
    Tendsto (fun n => P.truncatedPairedCylinderProbability (F n) E t) atTop
      (𝓝 (P.pairedCylinderProbability E t)) := by
  classical
  let test : Configuration → Configuration → ℝ≥0∞ :=
    fun initial η => if E initial ∧ E η then 1 else 0
  have htest : ∀ initial η ξ, (∀ v ∈ A, η v = ξ v) → test initial η = test initial ξ := by
    intro initial η ξ heq
    simp only [test, hlocal η ξ heq]
  have htest_meas : ∀ n,
      Measurable (fun ω => test (P.initial ω) (P.truncatedTrajectories (F n) ω t)) := by
    intro n
    exact Measurable.ite (hmeas n) measurable_const measurable_const
  have hn := P.tendsto_lintegral_truncated_test F hmono hex t A test htest 1 (by simp)
    (by intro initial η; dsimp [test]; split <;> simp) htest_meas
  have hleft (n : ℕ) :
      (∫⁻ ω, test (P.initial ω) (P.truncatedTrajectories (F n) ω t) ∂μ) =
        P.truncatedPairedCylinderProbability (F n) E t := by
    simpa only [Set.indicator, Set.mem_ofPred_eq, test, one_mul,
      truncatedPairedCylinderProbability] using lintegral_indicator_const (hmeas n) (1 : ℝ≥0∞)
  have hright : (∫⁻ ω, test (P.initial ω) (P.trajectories ω t) ∂μ) =
      P.pairedCylinderProbability E t := by
    simpa only [Set.indicator, Set.mem_ofPred_eq, test, one_mul,
      pairedCylinderProbability] using lintegral_indicator_const hfull (1 : ℝ≥0∞)
  simpa only [hleft, hright] using hn

/-- This specialization uses the previously proved locality of the actual
walk-defined one-arm event; only trajectory measurability remains explicit. -/
theorem tendsto_oneArm_pairedCylinderProbability (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (t : ℝ) (v : Site) (R : ℕ) (hv : v ∈ latticeBox R)
    (hfull : Measurable (fun ω => P.trajectories ω t))
    (hmeas : ∀ n, Measurable (fun ω => P.truncatedTrajectories (F n) ω t)) :
    Tendsto (fun n => P.truncatedPairedCylinderProbability (F n) (fun η => OneArm η v R) t)
      atTop (𝓝 (P.pairedCylinderProbability (fun η => OneArm η v R) t)) := by
  apply P.tendsto_pairedCylinderProbability F hmono hex t (latticeBox (R + 1))
  · intro η ξ heq
    exact oneArm_congr_of_eqOn_box hv (fun w hw => heq w hw)
  · exact ((measurableSet_oneArm v R).preimage P.measurable_initial).inter
      ((measurableSet_oneArm v R).preimage hfull)
  · intro n
    exact ((measurableSet_oneArm v R).preimage P.measurable_initial).inter
      ((measurableSet_oneArm v R).preimage (hmeas n))

theorem pairedCylinderProbability_zero (P : PoissonGraphicalRealization μ rate)
    (E : Configuration → Prop) :
    P.pairedCylinderProbability E 0 = μ {ω | E (P.initial ω)} := by
  simp only [pairedCylinderProbability, P.trajectories_zero, and_self]

end PoissonGraphicalRealization

set_option backward.isDefEq.respectTransparency.types false in
/-- Weighted Fatou permits an infinite weight. In particular it does not
discard or alter a positive-exponent Frostman kernel on the diagonal. -/
theorem weighted_lintegral_le_liminf {T : Type*} [MeasurableSpace T] (ν : Measure T)
    (weight : T → ℝ≥0∞) (Q : ℕ → T → ℝ≥0∞) (q : T → ℝ≥0∞)
    (hconv : ∀ t, Tendsto (fun n => Q n t) atTop (𝓝 (q t)))
    (hmeas : ∀ n, AEMeasurable (fun t => weight t * Q n t) ν) :
    (∫⁻ t, weight t * q t ∂ν) ≤ liminf (fun n => ∫⁻ t, weight t * Q n t ∂ν) atTop := by
  calc
    _ ≤ ∫⁻ t, liminf (fun n => weight t * Q n t) atTop ∂ν := by
      apply lintegral_mono
      intro t
      have h := ENNReal.le_liminf_mul (f := atTop)
        (u := fun _ : ℕ => weight t) (v := fun n => Q n t)
      have hmul : ((fun _ : ℕ => weight t) * (fun n => Q n t)) =
          (fun n => weight t * Q n t) := by
        funext n
        rfl
      rw [hmul, liminf_const, (hconv t).liminf_eq] at h
      exact h
    _ ≤ _ := lintegral_liminf_le' hmeas

theorem weighted_lintegral_bound_of_uniform {T : Type*} [MeasurableSpace T] (ν : Measure T)
    (weight : T → ℝ≥0∞) (Q : ℕ → T → ℝ≥0∞) (q : T → ℝ≥0∞)
    (hconv : ∀ t, Tendsto (fun n => Q n t) atTop (𝓝 (q t)))
    (hmeas : ∀ n, AEMeasurable (fun t => weight t * Q n t) ν)
    (B : ℝ≥0∞) (hbound : ∀ n, (∫⁻ t, weight t * Q n t ∂ν) ≤ B) :
    (∫⁻ t, weight t * q t ∂ν) ≤ B := by
  refine (weighted_lintegral_le_liminf ν weight Q q hconv hmeas).trans ?_
  calc
    _ ≤ liminf (fun _ : ℕ => B) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hbound)
    _ = B := liminf_const _

namespace PoissonGraphicalRealization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

noncomputable def correlationEnergy (P : PoissonGraphicalRealization μ rate)
    (E : Configuration → Prop) (γ : ℝ) (ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ t, frostmanKernel γ 0 t * P.pairedCylinderProbability E t ∂ν

noncomputable def truncatedCorrelationEnergy (P : PoissonGraphicalRealization μ rate)
    (F : Finset (Sym2 Site)) (E : Configuration → Prop) (γ : ℝ) (ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ t, frostmanKernel γ 0 t * P.truncatedPairedCylinderProbability F E t ∂ν

theorem correlation_integrand_at_zero (P : PoissonGraphicalRealization μ rate)
    (E : Configuration → Prop) {γ : ℝ} (hγ : 0 < γ)
    (hpositive : μ {ω | E (P.initial ω)} ≠ 0) :
    frostmanKernel γ 0 0 * P.pairedCylinderProbability E 0 = ⊤ := by
  rw [frostmanKernel_diagonal hγ, P.pairedCylinderProbability_zero]
  exact ENNReal.top_mul hpositive

/-- Uniform finite-edge energy bounds pass to the full actual clock process.
Take `ν = volume.restrict (Set.Ioc 0 1)` for the time-lag energy. Any geometric
or spectral origin of `hbound` remains a separate input. -/
theorem correlationEnergy_le_of_truncated_bound (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (A : Finset Site) (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ v ∈ A, η v = ξ v) → (E η ↔ E ξ))
    (hfull : ∀ t, MeasurableSet {ω | E (P.initial ω) ∧ E (P.trajectories ω t)})
    (hevents : ∀ n t, MeasurableSet {ω | E (P.initial ω) ∧ E (P.truncatedTrajectories (F n) ω t)})
    (γ : ℝ) (ν : Measure ℝ)
    (htime : ∀ n, AEMeasurable
      (fun t => frostmanKernel γ 0 t * P.truncatedPairedCylinderProbability (F n) E t) ν)
    (B : ℝ≥0∞) (hbound : ∀ n, P.truncatedCorrelationEnergy (F n) E γ ν ≤ B) :
    P.correlationEnergy E γ ν ≤ B := by
  exact weighted_lintegral_bound_of_uniform ν (frostmanKernel γ 0)
    (fun n => P.truncatedPairedCylinderProbability (F n) E)
    (P.pairedCylinderProbability E)
    (fun t => P.tendsto_pairedCylinderProbability F hmono hex t A E hlocal
      (hfull t) (fun n => hevents n t)) htime B hbound

/-- Direct energy transfer for the actual one-arm event, using its proved
finite-color locality rather than an assumed cylinder representation. -/
theorem oneArm_correlationEnergy_le_of_truncated_bound
    (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (v : Site) (R : ℕ) (hv : v ∈ latticeBox R)
    (hfull : ∀ t, Measurable (fun ω => P.trajectories ω t))
    (hevents : ∀ n t, Measurable (fun ω => P.truncatedTrajectories (F n) ω t))
    (γ : ℝ) (ν : Measure ℝ)
    (htime : ∀ n, AEMeasurable
      (fun t => frostmanKernel γ 0 t *
        P.truncatedPairedCylinderProbability (F n) (fun η => OneArm η v R) t) ν)
    (B : ℝ≥0∞)
    (hbound : ∀ n,
      P.truncatedCorrelationEnergy (F n) (fun η => OneArm η v R) γ ν ≤ B) :
    P.correlationEnergy (fun η => OneArm η v R) γ ν ≤ B := by
  apply P.correlationEnergy_le_of_truncated_bound F hmono hex (latticeBox (R + 1))
    (fun η => OneArm η v R) ?_ ?_ ?_ γ ν htime B hbound
  · intro η ξ heq
    exact oneArm_congr_of_eqOn_box hv (fun w hw => heq w hw)
  · intro t
    exact ((measurableSet_oneArm v R).preimage P.measurable_initial).inter
      ((measurableSet_oneArm v R).preimage (hfull t))
  · intro n t
    exact ((measurableSet_oneArm v R).preimage P.measurable_initial).inter
      ((measurableSet_oneArm v R).preimage (hevents n t))

end PoissonGraphicalRealization
end ExceptionalTimes

#print axioms ExceptionalTimes.PoissonGraphicalRealization.tendsto_lintegral_truncated_test
#print axioms ExceptionalTimes.PoissonGraphicalRealization.tendsto_oneArm_pairedCylinderProbability
#print axioms ExceptionalTimes.weighted_lintegral_le_liminf
#print axioms ExceptionalTimes.PoissonGraphicalRealization.correlationEnergy_le_of_truncated_bound
#print axioms ExceptionalTimes.PoissonGraphicalRealization.correlation_integrand_at_zero
#print axioms ExceptionalTimes.PoissonGraphicalRealization.oneArm_correlationEnergy_le_of_truncated_bound
