import ExceptionalTimes.ClockSpatial
import ExceptionalTimes.InvariantConullCore

/-! Raw independent clock data and its equivariant null-set repair.
This module proves a construction bridge. It does not assume or assert
existence of a Poisson clock law or backward nonexplosion. -/

open MeasureTheory Set
open scoped Classical

namespace ExceptionalTimes

structure PoissonClockInputs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (rate : Sym2 Site → ℝ) where
  initial : Ω → Configuration
  clocks : Ω → ClockField
  measurable_initial : Measurable initial
  measurable_counts : ∀ edge a b, Measurable (fun ω => (clocks ω).markCount edge a b)
  finite_counts : ∀ ω edge a b, ((clocks ω).marks edge ∩ Ioc a b).Finite
  independent_law : IndependentPoissonInitial μ rate initial clocks

namespace PoissonClockInputs

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

def emptyClocks : ClockField where
  marks _ := ∅
  positive_time _ _ h := h.elim
  diagonal_empty _ := rfl

theorem emptyClocks_noIncidentTies : emptyClocks.NoIncidentTies :=
  fun _ _ _ _ h => h.elim

theorem emptyClocks_finiteBackwardTraces : emptyClocks.HasFiniteBackwardTraces := by
  intro c v
  exact ⟨v,.stop (fun _ _ h => h.elim)⟩

theorem emptyClocks_finiteCounts (edge : Sym2 Site) (a b : ℝ) :
    (emptyClocks.marks edge ∩ Ioc a b).Finite := by
  simp only [emptyClocks,empty_inter]
  exact finite_empty

theorem emptyClocks_markCount (edge : Sym2 Site) (a b : ℝ) :
    emptyClocks.markCount edge a b = 0 := by simp [ClockField.markCount,emptyClocks]

def Good (D : PoissonClockInputs μ rate) (ω : Ω) : Prop :=
  (D.clocks ω).NoIncidentTies ∧ (D.clocks ω).HasFiniteBackwardTraces

noncomputable def repairedClocks (D : PoissonClockInputs μ rate) (G : Set Ω) (ω : Ω) : ClockField :=
  if ω ∈ G then D.clocks ω else emptyClocks

noncomputable def repair (D : PoissonClockInputs μ rate) (G : Set Ω)
    (hGm : MeasurableSet G) (hGae : ∀ᵐ ω ∂μ, ω ∈ G)
    (hGood : ∀ ω ∈ G, D.Good ω) : PoissonGraphicalRealization μ rate where
  initial := D.initial
  clocks := D.repairedClocks G
  measurable_initial := D.measurable_initial
  measurable_counts edge a b := by
    have heq : (fun ω => (D.repairedClocks G ω).markCount edge a b) =
        (fun ω => if ω ∈ G then (D.clocks ω).markCount edge a b else 0) := by
      funext ω
      by_cases hω : ω ∈ G <;> simp [repairedClocks,hω,emptyClocks_markCount]
    rw [heq]
    exact Measurable.ite hGm (D.measurable_counts edge a b) measurable_const
  finite_counts ω edge a b := by
    by_cases hω : ω ∈ G
    · simpa only [repairedClocks,ite_eq_left hω] using D.finite_counts ω edge a b
    · simpa only [repairedClocks,ite_eq_right hω] using emptyClocks_finiteCounts edge a b
  no_incident_ties ω := by
    by_cases hω : ω ∈ G
    · simpa only [repairedClocks,ite_eq_left hω] using (hGood ω hω).1
    · simpa only [repairedClocks,ite_eq_right hω] using emptyClocks_noIncidentTies
  finite_backward_traces ω := by
    by_cases hω : ω ∈ G
    · simpa only [repairedClocks,ite_eq_left hω] using (hGood ω hω).2
    · simpa only [repairedClocks,ite_eq_right hω] using emptyClocks_finiteBackwardTraces
  independent_law := by
    intro s η n T count
    rw [show μ {ω | (∀ v ∈ s, D.initial ω v = η v) ∧
        ∀ i, (D.repairedClocks G ω).markCount (T.edge i) (T.start i) (T.finish i) = count i} =
        μ {ω | (∀ v ∈ s, D.initial ω v = η v) ∧
        ∀ i, (D.clocks ω).markCount (T.edge i) (T.start i) (T.finish i) = count i} by
      apply measure_congr
      filter_upwards [hGae] with ω hω
      simp only [repairedClocks,ite_eq_left hω]]
    exact D.independent_law s η n T count

theorem repair_clocks_ae (D : PoissonClockInputs μ rate) (G : Set Ω)
    (hGm : MeasurableSet G) (hGae : ∀ᵐ ω ∂μ, ω ∈ G) (hGood : ∀ ω ∈ G, D.Good ω) :
    (D.repair G hGm hGae hGood).clocks =ᵐ[μ] D.clocks := by
  filter_upwards [hGae] with ω hω
  change (if ω ∈ G then D.clocks ω else emptyClocks) = D.clocks ω
  exact ite_eq_left hω

theorem repair_spatial_semiconj (D : PoissonClockInputs μ rate) (G : Set Ω)
    (hGm : MeasurableSet G) (hGae : ∀ᵐ ω ∂μ, ω ∈ G) (hGood : ∀ ω ∈ G, D.Good ω)
    (e : Ω → Ω) (z : Site) (hGinv : ∀ ω, e ω ∈ G ↔ ω ∈ G)
    (hinitial : ∀ ω, D.initial (e ω) = translateConfiguration z (D.initial ω))
    (hclocks : ∀ ω, D.clocks (e ω) = (D.clocks ω).spatialTranslate z) :
    Function.Semiconj (D.repair G hGm hGae hGood).trajectories e (translateTrajectory z) := by
  apply PoissonGraphicalRealization.trajectories_spatial_semiconj
    (D.repair G hGm hGae hGood) e z hinitial
  intro ω
  change D.repairedClocks G (e ω) = (D.repairedClocks G ω).spatialTranslate z
  by_cases hω : ω ∈ G
  · simp only [repairedClocks,ite_eq_left hω,ite_eq_left ((hGinv ω).mpr hω),hclocks]
  · have heω : e ω ∉ G := fun h => hω ((hGinv ω).mp h)
    simp only [repairedClocks,ite_eq_right hω,ite_eq_right heω]
    rfl

theorem exists_equivariant_realization (D : PoissonClockInputs μ rate)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ) (z : Site)
    (hinitial : ∀ ω, D.initial (e ω) = translateConfiguration z (D.initial ω))
    (hclocks : ∀ ω, D.clocks (e ω) = (D.clocks ω).spatialTranslate z)
    (hgood : ∀ᵐ ω ∂μ, D.Good ω) :
    ∃ P : PoissonGraphicalRealization μ rate, P.initial = D.initial ∧
      P.clocks =ᵐ[μ] D.clocks ∧ Function.Semiconj P.trajectories e (translateTrajectory z) := by
  obtain ⟨G,hGm,hGae,hGgood,hGinv⟩ :=
    InvariantConullCore.exists_invariant_conull_subset e he D.Good hgood
  exact ⟨D.repair G hGm hGae hGgood,rfl,D.repair_clocks_ae G hGm hGae hGgood,
    D.repair_spatial_semiconj G hGm hGae hGgood e z hGinv hinitial hclocks⟩

#print axioms exists_equivariant_realization

end PoissonClockInputs
end ExceptionalTimes
