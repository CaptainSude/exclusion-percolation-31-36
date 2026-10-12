import ExceptionalTimes.ClockTimeChange
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
A literal finite-dimensional law for fair initial colors and independent
Poisson clocks. Disjoint time intervals on the same unordered pair, and
arbitrary intervals on different pairs, have independent Poisson counts.
The joint cylinder formula includes the initial colors, so independence
of clocks from the initial coloring is part of the definition.

This file specifies the stochastic model. It does not assert existence
of a realization, stationarity, or exceptional times. A published graphical
construction must be matched to this definition before it can be invoked.
-/

namespace ExceptionalTimes

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators

namespace ClockField

noncomputable def markCount (C : ClockField) (edge : Sym2 Site) (a b : ℝ) : ℕ :=
  (C.marks edge ∩ Set.Ioc a b).ncard

theorem retime_marks_interval (C : ClockField) (e : ℝ ≃o ℝ) (hzero : e 0 = 0)
    (edge : Sym2 Site) (a b : ℝ) :
    (C.retime e hzero).marks edge ∩ Set.Ioc a b =
      e ⁻¹' (C.marks edge ∩ Set.Ioc (e a) (e b)) := by
  ext t
  simp [retime]

theorem retime_markCount (C : ClockField) (e : ℝ ≃o ℝ) (hzero : e 0 = 0)
    (edge : Sym2 Site) (a b : ℝ) :
    (C.retime e hzero).markCount edge a b = C.markCount edge (e a) (e b) := by
  unfold markCount
  rw [retime_marks_interval]
  exact Set.ncard_preimage_of_injective_subset_range e.injective
    (by simp [e.surjective.range_eq])

theorem speedup_markCount (C : ClockField) (a : ℝ) (ha : 0 < a)
    (edge : Sym2 Site) (s t : ℝ) :
    (C.speedup a ha).markCount edge s t = C.markCount edge (a * s) (a * t) :=
  C.retime_markCount (OrderIso.mulLeft₀ a ha) (mul_zero a) edge s t

theorem speedup_marks_interval (C : ClockField) (a : ℝ) (ha : 0 < a)
    (edge : Sym2 Site) (s t : ℝ) :
    (C.speedup a ha).marks edge ∩ Set.Ioc s t =
      (fun u : ℝ => a * u) ⁻¹' (C.marks edge ∩ Set.Ioc (a * s) (a * t)) :=
  C.retime_marks_interval (OrderIso.mulLeft₀ a ha) (mul_zero a) edge s t

end ClockField

/-- The standard Poisson mass, with real mean. Laws below use nonnegative means. -/
noncomputable def poissonMass (mean : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-mean) * mean ^ n / (n.factorial : ℝ))

/-- A finite collection of disjoint space-time clock tests. Edges are
unordered. Intervals may overlap only when the tested edges differ. -/
structure ClockTests (n : ℕ) where
  edge : Fin n → Sym2 Site
  start : Fin n → ℝ
  finish : Fin n → ℝ
  start_nonneg : ∀ i, 0 ≤ start i
  nonempty : ∀ i, start i < finish i
  disjoint : ∀ i j, i ≠ j → edge i = edge j →
    Disjoint (Set.Ioc (start i) (finish i)) (Set.Ioc (start j) (finish j))

namespace ClockTests

def empty : ClockTests 0 where
  edge := Fin.elim0
  start := Fin.elim0
  finish := Fin.elim0
  start_nonneg i := i.elim0
  nonempty i := i.elim0
  disjoint i := Fin.elim0 i

/-- Speed up endpoints of tests in the original clock field. -/
noncomputable def scale {n : ℕ} (T : ClockTests n) (a : ℝ) (ha : 0 < a) :
    ClockTests n where
  edge := T.edge
  start i := a * T.start i
  finish i := a * T.finish i
  start_nonneg i := mul_nonneg ha.le (T.start_nonneg i)
  nonempty i := mul_lt_mul_of_pos_left (T.nonempty i) ha
  disjoint i j hij he := by
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hi' : a⁻¹ * x ∈ Set.Ioc (T.start i) (T.finish i) := by
      constructor
      · have h := mul_lt_mul_of_pos_left hi.1 (inv_pos.mpr ha)
        simpa [← mul_assoc, ha.ne'] using h
      · have h := mul_le_mul_of_nonneg_left hi.2 (inv_nonneg.mpr ha.le)
        simpa [← mul_assoc, ha.ne'] using h
    have hj' : a⁻¹ * x ∈ Set.Ioc (T.start j) (T.finish j) := by
      constructor
      · have h := mul_lt_mul_of_pos_left hj.1 (inv_pos.mpr ha)
        simpa [← mul_assoc, ha.ne'] using h
      · have h := mul_le_mul_of_nonneg_left hj.2 (inv_nonneg.mpr ha.le)
        simpa [← mul_assoc, ha.ne'] using h
    exact Set.disjoint_left.mp (T.disjoint i j hij he) hi' hj'

end ClockTests

/-- Exact joint cylinder law of the independent initial colors and clocks.
The clock-count measurability and finiteness are supplied separately below. -/
def IndependentPoissonInitial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (rate : Sym2 Site → ℝ) (initial : Ω → Configuration)
    (clocks : Ω → ClockField) : Prop :=
  ∀ (s : Finset Site) (η : Configuration) (n : ℕ) (T : ClockTests n)
      (count : Fin n → ℕ),
    μ {ω | (∀ v ∈ s, initial ω v = η v) ∧
      ∀ i, (clocks ω).markCount (T.edge i) (T.start i) (T.finish i) = count i} =
      (1 / 2 : ℝ≥0∞) ^ s.card *
        ∏ i, poissonMass (rate (T.edge i) * (T.finish i - T.start i)) (count i)

theorem IndependentPoissonInitial.fair_initial
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rate : Sym2 Site → ℝ} {initial : Ω → Configuration} {clocks : Ω → ClockField}
    (hlaw : IndependentPoissonInitial μ rate initial clocks)
    (s : Finset Site) (η : Configuration) :
    μ {ω | ∀ v ∈ s, initial ω v = η v} = (1 / 2 : ℝ≥0∞) ^ s.card := by
  simpa using hlaw s η 0 ClockTests.empty Fin.elim0

theorem IndependentPoissonInitial.isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rate : Sym2 Site → ℝ} {initial : Ω → Configuration} {clocks : Ω → ClockField}
    (hlaw : IndependentPoissonInitial μ rate initial clocks) : IsProbabilityMeasure μ := by
  constructor
  simpa using hlaw.fair_initial ∅ (fun _ => false)

theorem IndependentPoissonInitial.speedup
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rate : Sym2 Site → ℝ} {initial : Ω → Configuration} {clocks : Ω → ClockField}
    (hlaw : IndependentPoissonInitial μ rate initial clocks) (a : ℝ) (ha : 0 < a) :
    IndependentPoissonInitial μ (fun edge => a * rate edge) initial
      (fun ω => (clocks ω).speedup a ha) := by
  intro s η n T count
  have h := hlaw s η n (T.scale a ha) count
  simp only [ClockTests.scale] at h
  simp only [ClockField.speedup_markCount]
  rw [h]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (fun mean => poissonMass mean (count i))
  ring

/-- A realization of the model on a probability space. The pathwise
regularity hypotheses here are the graphical construction obligations;
none is a correlation estimate or a dimension conclusion. -/
structure PoissonGraphicalRealization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (rate : Sym2 Site → ℝ) where
  initial : Ω → Configuration
  clocks : Ω → ClockField
  measurable_initial : Measurable initial
  measurable_counts : ∀ edge a b, Measurable (fun ω => (clocks ω).markCount edge a b)
  finite_counts : ∀ ω edge a b, ((clocks ω).marks edge ∩ Set.Ioc a b).Finite
  no_incident_ties : ∀ ω, (clocks ω).NoIncidentTies
  finite_backward_traces : ∀ ω, (clocks ω).HasFiniteBackwardTraces
  independent_law : IndependentPoissonInitial μ rate initial clocks

namespace PoissonGraphicalRealization

noncomputable def trajectories {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate) :
    Ω → Trajectory :=
  fun ω => (P.clocks ω).trajectory (P.finite_backward_traces ω) (P.initial ω)

theorem trajectories_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (ω : Ω) : P.trajectories ω 0 = P.initial ω :=
  ClockField.trajectory_zero (P.no_incident_ties ω) (P.finite_backward_traces ω) _

noncomputable def speedup {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (a : ℝ) (ha : 0 < a) : PoissonGraphicalRealization μ (fun edge => a * rate edge) where
  initial := P.initial
  clocks ω := (P.clocks ω).speedup a ha
  measurable_initial := P.measurable_initial
  measurable_counts edge s t := by
    simpa only [ClockField.speedup_markCount] using
      P.measurable_counts edge (a * s) (a * t)
  finite_counts ω edge s t := by
    rw [ClockField.speedup_marks_interval]
    exact (P.finite_counts ω edge (a * s) (a * t)).preimage
      (OrderIso.mulLeft₀ a ha).injective.injOn
  no_incident_ties ω := (P.no_incident_ties ω).retime _ _
  finite_backward_traces ω := (P.finite_backward_traces ω).retime _ _
  independent_law := P.independent_law.speedup a ha

theorem speedup_trajectories {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (a : ℝ) (ha : 0 < a) (ω : Ω) :
    (P.speedup a ha).trajectories ω = rescaleTime a (P.trajectories ω) :=
  ClockField.speedup_trajectory (P.clocks ω) (P.no_incident_ties ω)
    (P.finite_backward_traces ω) a ha (P.initial ω)

theorem almostSureConjecturedDimension_speedup {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (a : ℝ) (ha : 0 < a) (h : AlmostSureConjecturedDimension μ P.trajectories) :
    AlmostSureConjecturedDimension μ (P.speedup a ha).trajectories := by
  apply h.mono
  intro ω hω
  rw [speedup_trajectories]
  exact ExceptionalDimension.rescaleTime hω ha

end PoissonGraphicalRealization
end ExceptionalTimes

#print axioms ExceptionalTimes.ClockField.speedup_markCount
#print axioms ExceptionalTimes.IndependentPoissonInitial.fair_initial
#print axioms ExceptionalTimes.IndependentPoissonInitial.speedup
#print axioms ExceptionalTimes.PoissonGraphicalRealization.trajectories_zero
#print axioms ExceptionalTimes.PoissonGraphicalRealization.speedup_trajectories
#print axioms ExceptionalTimes.PoissonGraphicalRealization.almostSureConjecturedDimension_speedup
