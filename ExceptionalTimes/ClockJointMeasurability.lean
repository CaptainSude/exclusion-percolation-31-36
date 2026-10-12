import ExceptionalTimes.ClockCountMeasurability
import ExceptionalTimes.FiniteClockPointwiseGrid

/-! Exact joint measurability of the actual graphical process.
Pointwise count-grid reconstruction allows simultaneous disjoint rings;
finite-edge exhaustion then gives the literal full trajectory. -/

open MeasureTheory Set Filter
open scoped BigOperators Classical Topology

namespace ExceptionalTimes.ClockJointMeasurability

open FiniteClockBridge FiniteClockSlicePath FiniteClockWordLaw FiniteClockGridLaw
open FiniteClockParallelStep FiniteClockPointwiseGrid ClockCountMeasurability

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ}

omit [Fintype I] in
set_option maxHeartbeats 1000000 in
theorem measurable_variable_gridWord (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) (n : ℕ) :
    Measurable (fun p : Ω × ℝ => gridWord (P.clocks p.1) (siteEdges V edge) (p.2/n) n) := by
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro i
  change Measurable (fun p : Ω × ℝ => (P.clocks p.1).markCount (edgePair V edge i)
    ((j.val : ℝ)*(p.2/n)) (((j.val : ℝ)+1)*(p.2/n)))
  have hm : Measurable (fun p : Ω × ℝ =>
      (p.1,((j.val : ℝ)*(p.2/n),((j.val : ℝ)+1)*(p.2/n)))) := by fun_prop
  exact (measurable_interval_count P (edgePair V edge i)).comp hm

noncomputable def parallelGridApprox (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) (n : ℕ) (p : Ω × ℝ) : V → Bool :=
  runWord (parallelCubeUpdate V edge) (gridWord (P.clocks p.1) (siteEdges V edge) (p.2/n) n)
    (restrictColor V (P.initial p.1))

theorem measurable_parallelGridApprox (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) (n : ℕ) :
    Measurable (parallelGridApprox P V edge n) := by
  have hx : Measurable (fun p : Ω × ℝ => restrictColor V (P.initial p.1)) :=
    (Measurable.of_eval (fun v : V =>
      (measurable_pi_apply (v : Site)).comp P.measurable_initial)).comp measurable_fst
  exact (Measurable.of_discrete (f := fun q : (Fin n → I → ℕ) × (V → Bool) =>
    runWord (parallelCubeUpdate V edge) q.1 q.2)).comp
      ((measurable_variable_gridWord P V edge n).prodMk hx)

/-- Exact joint measurability, with no probability-zero modification and
no assumption that all simultaneous rings are absent. -/
theorem measurable_projectedTrajectory (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) :
    Measurable (fun p : Ω × ℝ => projectedTrajectory V (P.clocks p.1)
      (P.finiteEdgeCounts p.1) edge (P.initial p.1) p.2) := by
  let Z : ℕ → (Ω × ℝ) → (V → Bool) := fun n p =>
    if 0 < p.2 then parallelGridApprox P V edge n p else restrictColor V (P.initial p.1)
  have hm (n : ℕ) : Measurable (Z n) := by
    apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      (measurable_parallelGridApprox P V edge n)
    exact (Measurable.of_eval (fun v : V =>
      (measurable_pi_apply (v : Site)).comp P.measurable_initial)).comp measurable_fst
  apply measurable_of_tendsto_metrizable hm
  rw [tendsto_pi_nhds]
  intro p
  by_cases ht : 0 < p.2
  · have H := projected_parallelWord_of_good V (P.clocks p.1) (P.finiteEdgeCounts p.1)
      (P.no_incident_ties p.1) edge (P.initial p.1) p.2 ht
    apply tendsto_const_nhds.congr'
    filter_upwards [H] with n hn
    simpa only [Z,ite_eq_left ht,parallelGridApprox] using hn
  · have he : projectedTrajectory V (P.clocks p.1) (P.finiteEdgeCounts p.1) edge
        (P.initial p.1) p.2 = restrictColor V (P.initial p.1) := by
      unfold projectedTrajectory
      rw [ClockField.trajectory_nonpos ((P.no_incident_ties p.1).restrictEdges _)
        _ _ (le_of_not_gt ht)]
    simp only [Z,ite_eq_right ht,he]
    exact tendsto_const_nhds

/-- The unretained sites keep their measurable initial colors. -/
theorem measurable_truncated_of_array (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) :
    Measurable (fun p : Ω × ℝ => P.truncatedTrajectories (retainedEdges V edge) p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v ∈ V
  · exact (measurable_pi_apply (⟨v,hv⟩ : V)).comp (measurable_projectedTrajectory P V edge)
  · have he : (fun p : Ω × ℝ => P.truncatedTrajectories (retainedEdges V edge) p.1 p.2 v) =
        (fun p => P.initial p.1 v) := by
      funext p
      exact P.truncated_eq_initial_outside V edge p.1 p.2 hv
    rw [he]
    exact ((measurable_pi_apply v).comp P.measurable_initial).comp measurable_fst

omit [Fintype I] in
theorem measurable_truncated (P : PoissonGraphicalRealization μ rate) (F : Finset (Sym2 Site)) :
    Measurable (fun p : Ω × ℝ => P.truncatedTrajectories F p.1 p.2) := by
  let V := FiniteEdgeEnumeration.vertices F
  have H := measurable_truncated_of_array P V (FiniteEdgeEnumeration.enumerate F V (fun _ hv => hv))
  rw [FiniteEdgeEnumeration.enumerate_retainedEdges] at H
  exact H

omit [Fintype I] in
/-- The original realization axioms suffice for exact joint measurability
of its full, unmodified trajectory. -/
theorem measurable_trajectories (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n) :
    Measurable (fun p : Ω × ℝ => P.trajectories p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  apply measurable_of_tendsto_metrizable
    (fun n => (measurable_pi_apply v).comp (measurable_truncated P (F n)))
  rw [tendsto_pi_nhds]
  intro p
  obtain ⟨N,hN⟩ := P.eventually_truncated_trajectory_eq F hmono hex p.1 p.2 {v}
  apply tendsto_atTop_of_eventually_const (i₀ := N)
  intro n hn
  exact hN n hn v (Finset.mem_singleton_self v)

#print axioms measurable_projectedTrajectory
#print axioms measurable_trajectories

end ExceptionalTimes.ClockJointMeasurability
