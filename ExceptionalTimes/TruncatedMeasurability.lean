import ExceptionalTimes.FiniteClockGridLaw
import ExceptionalTimes.FiniteEdgeEnumeration

/-! The entire finite-clock configuration is almost-everywhere measurable,
including the unchanged colors outside the retained endpoint set. -/

namespace ExceptionalTimes

open MeasureTheory
open FiniteClockBridge FiniteClockGridLaw

theorem ClockField.trajectory_nonpos {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (η : Configuration) {t : ℝ} (htime : t ≤ 0) :
    C.trajectory hf η t = η := by
  funext v
  change η (C.ancestor hf (TimeCutoff.closedAt t) v) = η v
  congr 1
  apply ClockField.ancestor_eq_of_noEligibleRing ht hf
  intro w s hs ha
  exact (not_le_of_gt hs.pos) (ha.trans htime)

theorem ClockField.trajectory_eq_initial_of_no_rings {C : ClockField}
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces) (η : Configuration)
    (v : Site) (h : ∀ w t, ¬ C.Rings v w t) (t : ℝ) :
    C.trajectory hf η t v = η v := by
  change η (C.ancestor hf (TimeCutoff.closedAt t) v) = η v
  congr 1
  exact ClockField.ancestor_eq_of_noEligibleRing ht hf (fun w s hs _ => h w s hs)

theorem no_retained_rings_outside {I : Type*} [Fintype I] (V : Finset Site)
    (edge : I → V × V) (C : ClockField) {v : Site} (hv : v ∉ V) (w : Site) (t : ℝ) :
    ¬ (C.restrictEdges (retainedEdges V edge)).Rings v w t := by
  intro hr
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp
    ((ClockField.restrictEdges_rings C (retainedEdges V edge) v w t).mp hr).1
  rcases Sym2.eq_iff.mp hi with ⟨ha, _⟩ | ⟨_, ha⟩
  · exact hv (ha ▸ (edge i).1.property)
  · exact hv (ha ▸ (edge i).2.property)

namespace PoissonGraphicalRealization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

theorem truncated_nonpos (P : PoissonGraphicalRealization μ rate)
    (F : Finset (Sym2 Site)) (ω : Ω) {t : ℝ} (htime : t ≤ 0) :
    P.truncatedTrajectories F ω t = P.initial ω :=
  ClockField.trajectory_nonpos ((P.no_incident_ties ω).restrictEdges F) _ _ htime

theorem truncated_eq_initial_outside {I : Type*} [Fintype I]
    (P : PoissonGraphicalRealization μ rate) (V : Finset Site) (edge : I → V × V)
    (ω : Ω) (t : ℝ) {v : Site} (hv : v ∉ V) :
    P.truncatedTrajectories (retainedEdges V edge) ω t v = P.initial ω v := by
  exact ClockField.trajectory_eq_initial_of_no_rings
    ((P.no_incident_ties ω).restrictEdges _) _ _ v
    (no_retained_rings_outside V edge (P.clocks ω) hv) t

theorem aemeasurable_truncated_of_array {I : Type*} [Fintype I] [DecidableEq I]
    (P : PoissonGraphicalRealization μ rate) (V : Finset Site) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i)) (t : ℝ) :
    AEMeasurable (fun ω => P.truncatedTrajectories (retainedEdges V edge) ω t) μ := by
  by_cases ht : 0 < t
  · apply AEMeasurable.of_eval
    intro v
    by_cases hv : v ∈ V
    · exact (aemeasurable_projectedTrajectory V P edge hinj hr t ht).eval ⟨v, hv⟩
    · have heq : (fun ω => P.truncatedTrajectories (retainedEdges V edge) ω t v) =
          fun ω => P.initial ω v := by
        funext ω
        exact P.truncated_eq_initial_outside V edge ω t hv
      rw [heq]
      exact P.measurable_initial.aemeasurable.eval v
  · have heq : (fun ω => P.truncatedTrajectories (retainedEdges V edge) ω t) = P.initial := by
      funext ω
      exact P.truncated_nonpos _ ω (le_of_not_gt ht)
    rw [heq]
    exact P.measurable_initial.aemeasurable

theorem aemeasurable_truncated (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : Finset (Sym2 Site)) (t : ℝ) :
    AEMeasurable (fun ω => P.truncatedTrajectories F ω t) μ := by
  classical
  let V := FiniteEdgeEnumeration.vertices F
  have h := P.aemeasurable_truncated_of_array V
    (FiniteEdgeEnumeration.enumerate F V le_rfl)
    (FiniteEdgeEnumeration.enumerate_injective F V le_rfl)
    (fun i => hr _) t
  simpa only [FiniteEdgeEnumeration.enumerate_retainedEdges] using h

theorem aemeasurable_trajectories_of_exhaustion (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n) (t : ℝ) :
    AEMeasurable (fun ω => P.trajectories ω t) μ := by
  apply AEMeasurable.of_eval
  intro v
  apply aemeasurable_of_tendsto_metrizable_ae Filter.atTop
    (fun n => (P.aemeasurable_truncated hr (F n) t).eval v)
  apply ae_of_all μ
  intro ω
  obtain ⟨N, hN⟩ := P.eventually_truncated_trajectory_eq F hmono hex ω t {v}
  exact tendsto_atTop_of_eventually_const (i₀ := N)
    (fun n hn => hN n hn v (Finset.mem_singleton_self v))

end PoissonGraphicalRealization
end ExceptionalTimes

#print axioms ExceptionalTimes.PoissonGraphicalRealization.aemeasurable_truncated_of_array
#print axioms ExceptionalTimes.PoissonGraphicalRealization.aemeasurable_trajectories_of_exhaustion
