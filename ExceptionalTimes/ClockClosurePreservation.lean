import ExceptionalTimes.ClockPathRegularity
import ExceptionalTimes.ClockIncidentFiniteness
import ExceptionalTimes.ClockNoGlobalTies
import ExceptionalTimes.FiniteRecoloring

/-! Actual site-time closure preserves existence of an infinite cluster.
Only two colors can change at a clock time, and finite recoloring cannot
destroy every infinite cluster on this locally finite lattice. -/

open MeasureTheory Set
open scoped Classical

namespace ExceptionalTimes.ClockClosurePreservation

theorem hasInfiniteBlackCluster_of_closedColors (C : ClockField)
    (hties : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    (hloc : C.LocallyFiniteIncident)
    (hglobal : ∀ e f s, s ∈ C.marks e → s ∈ C.marks f → e = f)
    (η : Configuration) (t : ℝ) (ht : 0 ≤ t)
    (h : HasInfiniteBlackCluster (TimeClosure.closedColors (C.trajectory hf η) t)) :
    HasInfiniteBlackCluster (C.trajectory hf η t) := by
  by_cases hring : ∃ u w, C.Rings u w t
  · obtain ⟨u,w,hring⟩ := hring
    apply FiniteRecoloring.hasInfiniteBlackCluster_of_finite_changes
      (S := {u,w}) ((Set.finite_singleton w).insert u) ?_ h
    intro v hv
    have hvu : v ≠ u := fun heq => hv (by simp [heq])
    have hvw : v ≠ w := fun heq => hv (by simp [heq])
    exact ClockPathRegularity.closedColors_eq_outside_ring C hties hf hloc η
      hring hglobal v hvu hvw
  · have heq : TimeClosure.closedColors (C.trajectory hf η) t = C.trajectory hf η t := by
      funext v
      apply ClockPathRegularity.closedColors_eq_without_mark C hties hf hloc η v t ht
      intro w hw
      exact hring ⟨v,w,hw⟩
    rwa [heq] at h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

theorem ae_closure_preserves_percolation (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (hsum : ∀ v, Summable (fun w => rate s(v,w))) :
    ∀ᵐ ω ∂μ, ∀ v t, 0 ≤ t →
      (BlackCluster (TimeClosure.closedColors (P.trajectories ω) t) v).Infinite →
        HasInfiniteBlackCluster (P.trajectories ω t) := by
  filter_upwards [ClockIncidentFiniteness.ae_locallyFiniteIncident P hsum,
    ClockNoGlobalTies.ae_no_global_ties P hr] with ω hloc hglobal
  intro v t ht hv
  exact hasInfiniteBlackCluster_of_closedColors (P.clocks ω) (P.no_incident_ties ω)
    (P.finite_backward_traces ω) hloc hglobal (P.initial ω) t ht ⟨v,hv⟩

theorem ae_closure_preserves_percolation_kernel (k : RateKernel)
    (P : PoissonGraphicalRealization μ k.unorderedPairRate) :
    ∀ᵐ ω ∂μ, ∀ v t, 0 ≤ t →
      (BlackCluster (TimeClosure.closedColors (P.trajectories ω) t) v).Infinite →
        HasInfiniteBlackCluster (P.trajectories ω t) := by
  apply ae_closure_preserves_percolation P ?_ k.pairRate_summable
  intro e
  induction e using Sym2.ind with
  | _ u v => exact k.pairRate_nonneg u v

theorem ae_siteClosurePreservesPercolationAt (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (hsum : ∀ v, Summable (fun w => rate s(v,w))) (v : Site) :
    ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (P.trajectories ω) v :=
  (ae_closure_preserves_percolation P hr hsum).mono (fun _ h => h v)

theorem ae_siteClosurePreservesPercolationAt_kernel (k : RateKernel)
    (P : PoissonGraphicalRealization μ k.unorderedPairRate) (v : Site) :
    ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (P.trajectories ω) v :=
  (ae_closure_preserves_percolation_kernel k P).mono (fun _ h => h v)

#print axioms ae_closure_preserves_percolation_kernel
#print axioms ae_siteClosurePreservesPercolationAt_kernel

end ExceptionalTimes.ClockClosurePreservation
