import ExceptionalTimes.FiniteClockShiftedGrid

/-! Two-time stationarity of the actual finite graphical process, proved
from independent Poisson count cylinders and chronological grid limits. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical Topology

namespace ExceptionalTimes.FiniteClockStationarity

open FiniteClockWordLaw FiniteClockBridge FiniteClockGridLaw FiniteClockSlices
open FiniteClockSlicePath FiniteClockFutureLaw FiniteClockShiftedGrid

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def shiftTests {J : Type*} (T : IndexedTests J) (s : ℝ) (hs : 0 ≤ s) : IndexedTests J where
  edge := T.edge
  start j := s+T.start j
  finish j := s+T.finish j
  start_nonneg j := add_nonneg hs (T.start_nonneg j)
  nonempty j := by linarith [T.nonempty j]
  disjoint i j hij he := by
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hi' : x-s ∈ Set.Ioc (T.start i) (T.finish i) :=
      ⟨by linarith [hi.1],by linarith [hi.2]⟩
    have hj' : x-s ∈ Set.Ioc (T.start j) (T.finish j) :=
      ⟨by linarith [hj.1],by linarith [hj.2]⟩
    exact Set.disjoint_left.mp (T.disjoint i j hij he) hi' hj'

theorem tendsto_event_of_discrepancy {Ω S T : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : Ω → T) (Y : Ω → S) (Z : ℕ → Ω → S)
    (E : T → S → Prop)
    (he : Tendsto (fun n => μ {ω | Y ω ≠ Z n ω}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {ω | E (X ω) (Z n ω)}) atTop
      (𝓝 (μ {ω | E (X ω) (Y ω)})) := by
  have hlo := ENNReal.Tendsto.sub
    (tendsto_const_nhds (x := μ {ω | E (X ω) (Y ω)})) he (Or.inr ENNReal.zero_ne_top)
  have hhi := (tendsto_const_nhds (x := μ {ω | E (X ω) (Y ω)})).add he
  simp only [tsub_zero,add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro n
    apply tsub_le_iff_right.mpr
    exact measure_event_le_of_discrepancy_aux X Y (Z n) E
  · intro n
    simpa only [ne_comm] using measure_event_le_of_discrepancy_aux X (Z n) Y E

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ}

theorem shifted_joint_count_law (V : Finset Site) (P : PoissonGraphicalRealization μ rate)
    (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (s h : ℝ) (hs : 0 < s) (hh : 0 < h) (n : ℕ)
    (η : V → Bool) (w : Fin n → I → ℕ) :
    μ {ω | projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) s = η ∧
      shiftedWord (P.clocks ω) (siteEdges V edge) s h n = w} =
      (1/2 : ℝ≥0∞)^V.card * ∏ j,productMass (fun i => rate (edgePair V edge i)*h) (w j) := by
  let T := shiftTests (gridTests (edgePair V edge) hinj n h hh) s hs.le
  have hT (j : Fin n × I) : s ≤ T.start j := by
    dsimp [T,shiftTests,gridTests]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have H := projected_uniform_future_counts P V edge hinj hr s hs T hT η (fun ji => w ji.1 ji.2)
  have hmean : (fun ji : Fin n × I => rate (T.edge ji)*(T.finish ji-T.start ji)) =
      (fun ji => rate (edgePair V edge ji.2)*h) := by
    funext ji
    dsimp [T,shiftTests,gridTests]
    ring
  rw [hmean] at H
  simpa only [shiftedWord,sliceCounts,pairIndex,siteEdges,edgePair,T,shiftTests,gridTests,
    productMass,Fintype.prod_prod_type,funext_iff,Prod.forall] using H

theorem shifted_grid_event_eq (V : Finset Site) (P : PoissonGraphicalRealization μ rate)
    (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (s h : ℝ) (hs : 0 < s) (hh : 0 < h) (n : ℕ)
    (E : (V → Bool) → (V → Bool) → Prop) :
    μ {ω | E (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) s)
      (shiftedApprox V P edge s h n ω)} =
    μ {ω | E (restrictColor V (P.initial ω)) (gridApprox V P edge h n ω)} := by
  let X := fun ω => (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
    edge (P.initial ω) s,shiftedWord (P.clocks ω) (siteEdges V edge) s h n)
  let Y := fun ω => (restrictColor V (P.initial ω),gridWord (P.clocks ω) (siteEdges V edge) h n)
  have hX : AEMeasurable X μ :=
    (aemeasurable_projectedTrajectory V P edge hinj hr s hs).prodMk
      (Measurable.of_eval (fun j => Measurable.of_eval (fun i => P.measurable_counts _ _ _))).aemeasurable
  have hY : Measurable Y :=
    (Measurable.of_eval (fun v : V => (measurable_pi_apply (v : Site)).comp P.measurable_initial)).prodMk
      (measurable_gridWord V P edge h n)
  have hm : μ.map X = μ.map Y := by
    apply Measure.ext_of_singleton
    rintro ⟨η,w⟩
    rw [Measure.map_apply_of_aemeasurable hX (measurableSet_singleton _),
      Measure.map_apply hY (measurableSet_singleton _)]
    change μ {ω | X ω = (η,w)} = μ {ω | Y ω = (η,w)}
    simp only [X,Y,Prod.mk.injEq]
    rw [shifted_joint_count_law V P edge hinj hr s h hs hh n,
      grid_joint_count_law V P edge hinj n h hh]
  let A : Set ((V → Bool) × (Fin n → I → ℕ)) :=
    {p | E p.1 (runWord (cubeUpdate V edge) p.2 p.1)}
  change μ (X ⁻¹' A) = μ (Y ⁻¹' A)
  rw [← Measure.map_apply_of_aemeasurable hX (MeasurableSet.of_discrete),
    ← Measure.map_apply hY (MeasurableSet.of_discrete),hm]

/-- Finite-dimensional two-time stationarity, for any two-state event. -/
theorem projected_stationary (V : Finset Site) (P : PoissonGraphicalRealization μ rate)
    (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (E : (V → Bool) → (V → Bool) → Prop) :
    μ {ω | E (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) s)
      (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) (s+t))} =
    μ {ω | E (restrictColor V (P.initial ω))
      (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t)} := by
  apply event_probability_eq_of_approximation_aux
    (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) s)
    (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) (s+t))
    (fun n => shiftedApprox V P edge s (t/n) n) E
  · have H := tendsto_event_of_discrepancy
      (fun ω => restrictColor V (P.initial ω))
      (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t)
      (fun n => gridApprox V P edge (t/n) n) E
      (tendsto_projected_discrepancy V P edge hinj hr t ht)
    apply H.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact (shifted_grid_event_eq V P edge hinj hr s (t/n) hs (div_pos ht hn') n E).symm
  · exact tendsto_shifted_discrepancy V P edge hinj hr s t hs.le ht

#print axioms shifted_joint_count_law
#print axioms projected_stationary

end ExceptionalTimes.FiniteClockStationarity
