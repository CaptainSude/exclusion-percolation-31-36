import ExceptionalTimes.ClockTruncationLimit

/-! Finite-edge probability and energy limits need only measurability in
the completed probability space. No completeness is imposed on the space. -/

namespace ExceptionalTimes

open MeasureTheory Filter
open scoped ENNReal Topology

theorem weighted_lintegral_bound_of_eventual {T : Type*} [MeasurableSpace T] (ν : Measure T)
    (weight : T → ℝ≥0∞) (Q : ℕ → T → ℝ≥0∞) (q : T → ℝ≥0∞)
    (hconv : ∀ t, Tendsto (fun n => Q n t) atTop (𝓝 (q t)))
    (hmeas : ∀ n, AEMeasurable (fun t => weight t * Q n t) ν)
    (B : ℝ≥0∞) (hbound : ∀ᶠ n in atTop, (∫⁻ t, weight t * Q n t ∂ν) ≤ B) :
    (∫⁻ t, weight t * q t ∂ν) ≤ B := by
  refine (weighted_lintegral_le_liminf ν weight Q q hconv hmeas).trans ?_
  calc
    _ ≤ liminf (fun _ : ℕ => B) atTop := Filter.liminf_le_liminf hbound
    _ = B := liminf_const _

namespace PoissonGraphicalRealization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

theorem tendsto_pairedCylinderProbability_of_nullMeasurable
    (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (t : ℝ) (A : Finset Site) (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ v ∈ A, η v = ξ v) → (E η ↔ E ξ))
    (hfull : NullMeasurableSet {ω | E (P.initial ω) ∧ E (P.trajectories ω t)} μ)
    (hmeas : ∀ n, NullMeasurableSet
      {ω | E (P.initial ω) ∧ E (P.truncatedTrajectories (F n) ω t)} μ) :
    Tendsto (fun n => P.truncatedPairedCylinderProbability (F n) E t) atTop
      (𝓝 (P.pairedCylinderProbability E t)) := by
  classical
  let : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  let test : Configuration → Configuration → ℝ≥0∞ :=
    fun initial η => if E initial ∧ E η then 1 else 0
  have htest : ∀ initial η ξ, (∀ v ∈ A, η v = ξ v) → test initial η = test initial ξ := by
    intro initial η ξ heq
    simp only [test, hlocal η ξ heq]
  have htest_meas : ∀ n,
      AEMeasurable (fun ω => test (P.initial ω) (P.truncatedTrajectories (F n) ω t)) μ := by
    intro n
    have hi := (aemeasurable_const (b := (1 : ℝ≥0∞))).indicator₀ (hmeas n)
    convert hi using 1
    funext ω
    simp [test, Set.indicator_apply]
  have hn : Tendsto
      (fun n => ∫⁻ ω, test (P.initial ω) (P.truncatedTrajectories (F n) ω t) ∂μ)
      atTop (𝓝 (∫⁻ ω, test (P.initial ω) (P.trajectories ω t) ∂μ)) := by
    apply tendsto_lintegral_of_dominated_convergence' (fun _ => 1) htest_meas
    · intro n
      exact ae_of_all μ (fun ω => by dsimp [test]; split <;> simp)
    · simp
    · apply ae_of_all μ
      intro ω
      obtain ⟨N, hN⟩ := P.eventually_truncated_two_time_test_eq F hmono hex t A test htest ω
      exact tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => hN n hn)
  have hleft (n : ℕ) :
      (∫⁻ ω, test (P.initial ω) (P.truncatedTrajectories (F n) ω t) ∂μ) =
        P.truncatedPairedCylinderProbability (F n) E t := by
    simpa only [Set.indicator, Set.mem_ofPred_eq, test, one_mul,
      truncatedPairedCylinderProbability] using lintegral_indicator_const₀ (hmeas n) (1 : ℝ≥0∞)
  have hright : (∫⁻ ω, test (P.initial ω) (P.trajectories ω t) ∂μ) =
      P.pairedCylinderProbability E t := by
    simpa only [Set.indicator, Set.mem_ofPred_eq, test, one_mul,
      pairedCylinderProbability] using lintegral_indicator_const₀ hfull (1 : ℝ≥0∞)
  simpa only [hleft, hright] using hn

theorem oneArm_correlationEnergy_le_of_truncated_bound_ae
    (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (v : Site) (R : ℕ) (hv : v ∈ latticeBox R)
    (hfull : ∀ t, AEMeasurable (fun ω => P.trajectories ω t) μ)
    (hevents : ∀ n t, AEMeasurable (fun ω => P.truncatedTrajectories (F n) ω t) μ)
    (γ : ℝ) (ν : Measure ℝ)
    (htime : ∀ n, AEMeasurable
      (fun t => frostmanKernel γ 0 t *
        P.truncatedPairedCylinderProbability (F n) (fun η => OneArm η v R) t) ν)
    (B : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop,
      P.truncatedCorrelationEnergy (F n) (fun η => OneArm η v R) γ ν ≤ B) :
    P.correlationEnergy (fun η => OneArm η v R) γ ν ≤ B := by
  apply weighted_lintegral_bound_of_eventual ν (frostmanKernel γ 0)
    (fun n => P.truncatedPairedCylinderProbability (F n) (fun η => OneArm η v R))
    (P.pairedCylinderProbability (fun η => OneArm η v R)) ?_ htime B hbound
  intro t
  apply P.tendsto_pairedCylinderProbability_of_nullMeasurable F hmono hex t
    (latticeBox (R + 1)) (fun η => OneArm η v R)
  · intro η ξ heq
    exact oneArm_congr_of_eqOn_box hv (fun w hw => heq w hw)
  · exact (((measurableSet_oneArm v R).preimage P.measurable_initial).nullMeasurableSet).inter
      ((hfull t).nullMeasurableSet_preimage (measurableSet_oneArm v R))
  · intro n
    exact (((measurableSet_oneArm v R).preimage P.measurable_initial).nullMeasurableSet).inter
      ((hevents n t).nullMeasurableSet_preimage (measurableSet_oneArm v R))

end PoissonGraphicalRealization
end ExceptionalTimes

#print axioms ExceptionalTimes.PoissonGraphicalRealization.oneArm_correlationEnergy_le_of_truncated_bound_ae
