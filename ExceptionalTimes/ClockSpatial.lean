import ExceptionalTimes.StochasticModel
import ExceptionalTimes.SpatialInvariance

/-! Spatial relabeling of actual clock traces and color transport. This is
the deterministic equivariance needed when applying spatial ergodicity of
the underlying independent randomness. No ergodicity input is asserted. -/

namespace ExceptionalTimes.ClockField

def relabel (C : ClockField) (g : Site ≃ Site) : ClockField where
  marks edge := C.marks (edge.map g.symm)
  positive_time edge t ht := C.positive_time _ t ht
  diagonal_empty v := by simpa using C.diagonal_empty (g.symm v)

theorem relabel_rings (C : ClockField) (g : Site ≃ Site) (u v : Site) (t : ℝ) :
    (C.relabel g).Rings (g u) (g v) t ↔ C.Rings u v t := by
  simp [Rings, relabel]

theorem NoIncidentTies.relabel {C : ClockField} (h : C.NoIncidentTies)
    (g : Site ≃ Site) : (C.relabel g).NoIncidentTies := by
  intro u v w t huv huw
  apply g.symm.injective
  exact h (g.symm u) (g.symm v) (g.symm w) t huv huw

theorem BackwardTrace.relabel {C : ClockField} {c : TimeCutoff} {v a : Site}
    (p : C.BackwardTrace c v a) (g : Site ≃ Site) :
    (C.relabel g).BackwardTrace c (g v) (g a) := by
  induction p with
  | @stop c v h =>
      apply BackwardTrace.stop
      intro w s hs ha
      have hr : C.Rings v (g.symm w) s := by
        change C.Rings (g.symm (g v)) (g.symm w) s at hs
        simpa using hs
      exact h (g.symm w) s hr ha
  | @jump c v s w a h tail ih =>
      apply BackwardTrace.jump (s := s) (w := g w) _ ih
      refine ⟨(relabel_rings C g v w s).mpr h.rings, h.allowed, ?_⟩
      intro z r hr ha
      apply h.latest (g.symm z) r _ ha
      change C.Rings (g.symm (g v)) (g.symm z) r at hr
      simpa using hr

theorem HasFiniteBackwardTraces.relabel {C : ClockField}
    (h : C.HasFiniteBackwardTraces) (g : Site ≃ Site) :
    (C.relabel g).HasFiniteBackwardTraces := by
  intro c v
  obtain ⟨a, ha⟩ := h c (g.symm v)
  exact ⟨g a, by simpa using ha.relabel g⟩

theorem relabel_ancestor (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (g : Site ≃ Site) (c : TimeCutoff) (v : Site) :
    (C.relabel g).ancestor (hf.relabel g) c v = g (C.ancestor hf c (g.symm v)) := by
  apply ancestor_eq_of_trace (ht.relabel g)
  simpa using (C.ancestor_trace hf c (g.symm v)).relabel g

theorem relabel_trajectory (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (g : Site ≃ Site) (η : Configuration)
    (t : ℝ) (v : Site) :
    (C.relabel g).trajectory (hf.relabel g) (η ∘ g.symm) t v =
      C.trajectory hf η t (g.symm v) := by
  change η (g.symm ((C.relabel g).ancestor _ (TimeCutoff.closedAt t) v)) = _
  rw [relabel_ancestor C ht hf, Equiv.symm_apply_apply]
  rfl

def spatialTranslate (C : ClockField) (z : Site) : ClockField :=
  C.relabel (Equiv.addRight z)

theorem spatialTranslate_trajectory (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (z : Site) (η : Configuration) :
    (C.spatialTranslate z).trajectory (hf.relabel (Equiv.addRight z))
      (translateConfiguration z η) = translateTrajectory z (C.trajectory hf η) := by
  funext t v
  exact relabel_trajectory C ht hf (Equiv.addRight z) η t v

theorem trajectory_congr {C D : ClockField} (hCD : C = D)
    (hfC : C.HasFiniteBackwardTraces) (hfD : D.HasFiniteBackwardTraces)
    {η θ : Configuration} (hηθ : η = θ) : C.trajectory hfC η = D.trajectory hfD θ := by
  cases hCD
  cases hηθ
  rfl

end ExceptionalTimes.ClockField

namespace ExceptionalTimes.PoissonGraphicalRealization

open MeasureTheory

theorem trajectories_spatial_semiconj
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (e : Ω → Ω) (z : Site)
    (hinitial : ∀ ω, P.initial (e ω) = translateConfiguration z (P.initial ω))
    (hclocks : ∀ ω, P.clocks (e ω) = (P.clocks ω).spatialTranslate z) :
    Function.Semiconj P.trajectories e (translateTrajectory z) := by
  intro ω
  unfold trajectories
  have h := ClockField.spatialTranslate_trajectory (P.clocks ω)
    (P.no_incident_ties ω) (P.finite_backward_traces ω) z (P.initial ω)
  exact (ClockField.trajectory_congr (hclocks ω) _ _ (hinitial ω)).trans h

end ExceptionalTimes.PoissonGraphicalRealization

#print axioms ExceptionalTimes.ClockField.spatialTranslate_trajectory
#print axioms ExceptionalTimes.PoissonGraphicalRealization.trajectories_spatial_semiconj
