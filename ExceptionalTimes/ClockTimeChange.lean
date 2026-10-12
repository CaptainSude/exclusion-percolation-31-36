import ExceptionalTimes.GraphicalProcess

/-!
Deterministic change of the actual clock marks. This links color transport
to time change of the trajectory; the Hausdorff-dimension consequence uses
the already proved invariance under positive linear rescaling.

The law of rescaled Poisson clocks is not assumed or constructed here.
-/

namespace ExceptionalTimes

set_option autoImplicit false
open scoped ENNReal

namespace TimeCutoff

def map (e : ℝ ≃o ℝ) (c : TimeCutoff) : TimeCutoff := ⟨e c.time, c.closed⟩

theorem allows_map (e : ℝ ≃o ℝ) (c : TimeCutoff) (s : ℝ) :
    (c.map e).Allows (e s) ↔ c.Allows s := by
  cases h : c.closed <;> simp [Allows, map, h]

theorem allows_map_symm (e : ℝ ≃o ℝ) (c : TimeCutoff) (s : ℝ) :
    (c.map e.symm).Allows s ↔ c.Allows (e s) := by
  simpa using allows_map e.symm c (e s)

@[simp]
theorem map_symm_map (e : ℝ ≃o ℝ) (c : TimeCutoff) :
    (c.map e).map e.symm = c := by
  cases c
  simp [map]

end TimeCutoff

namespace ClockField

/-- Pull clock marks back by an increasing bijection fixing the initial time. -/
def retime (C : ClockField) (e : ℝ ≃o ℝ) (hzero : e 0 = 0) : ClockField where
  marks edge := e ⁻¹' C.marks edge
  positive_time edge t ht := by
    have h := C.positive_time edge (e t) ht
    rw [← hzero] at h
    exact e.lt_iff_lt.mp h
  diagonal_empty v := by simp [C.diagonal_empty]

@[simp]
theorem retime_rings (C : ClockField) (e : ℝ ≃o ℝ) (hzero : e 0 = 0)
    (u v : Site) (t : ℝ) :
    (C.retime e hzero).Rings u v t ↔ C.Rings u v (e t) := Iff.rfl

theorem NoIncidentTies.retime {C : ClockField} (ht : C.NoIncidentTies)
    (e : ℝ ≃o ℝ) (hzero : e 0 = 0) : (C.retime e hzero).NoIncidentTies := by
  intro u v w t huv huw
  exact ht u v w (e t) huv huw

theorem BackwardTrace.retime {C : ClockField} {c : TimeCutoff} {v a : Site}
    (p : C.BackwardTrace c v a) (e : ℝ ≃o ℝ) (hzero : e 0 = 0) :
    (C.retime e hzero).BackwardTrace (c.map e.symm) v a := by
  induction p with
  | stop h =>
      apply BackwardTrace.stop
      intro w s hs ha
      exact h w (e s) hs ((TimeCutoff.allows_map_symm e _ s).mp ha)
  | @jump c v s w a h tail ih =>
      apply BackwardTrace.jump (s := e.symm s) (w := w)
      · refine ⟨?_, ?_, ?_⟩
        · change C.Rings v w (e (e.symm s))
          simpa using h.rings
        · exact (TimeCutoff.allows_map e.symm c s).mpr h.allowed
        · intro z r hr ha
          have hle := h.latest z (e r) hr
            ((TimeCutoff.allows_map_symm e c r).mp ha)
          simpa using e.symm.monotone hle
      · exact ih

theorem HasFiniteBackwardTraces.retime {C : ClockField}
    (hf : C.HasFiniteBackwardTraces) (e : ℝ ≃o ℝ) (hzero : e 0 = 0) :
    (C.retime e hzero).HasFiniteBackwardTraces := by
  intro c v
  obtain ⟨a, ha⟩ := hf (c.map e) v
  exact ⟨a, by simpa using ha.retime e hzero⟩

theorem retime_ancestor (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (e : ℝ ≃o ℝ) (hzero : e 0 = 0)
    (c : TimeCutoff) (v : Site) :
    (C.retime e hzero).ancestor (hf.retime e hzero) c v =
      C.ancestor hf (c.map e) v := by
  apply ancestor_eq_of_trace (ht.retime e hzero)
  simpa using (C.ancestor_trace hf (c.map e) v).retime e hzero

theorem retime_trajectory (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (e : ℝ ≃o ℝ) (hzero : e 0 = 0)
    (ω : Configuration) (t : ℝ) :
    (C.retime e hzero).trajectory (hf.retime e hzero) ω t =
      C.trajectory hf ω (e t) := by
  funext v
  change ω ((C.retime e hzero).ancestor _ (TimeCutoff.closedAt t) v) = _
  rw [retime_ancestor C ht hf]
  rfl

/-- Multiply every clock rate by `a` by dividing every realized mark by `a`. -/
noncomputable def speedup (C : ClockField) (a : ℝ) (ha : 0 < a) : ClockField :=
  C.retime (OrderIso.mulLeft₀ a ha) (mul_zero a)

theorem speedup_rings (C : ClockField) (a : ℝ) (ha : 0 < a)
    (u v : Site) (t : ℝ) :
    (C.speedup a ha).Rings u v t ↔ C.Rings u v (a * t) := Iff.rfl

theorem speedup_trajectory (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (a : ℝ) (ha : 0 < a) (ω : Configuration) :
    (C.speedup a ha).trajectory
        (hf.retime (OrderIso.mulLeft₀ a ha) (mul_zero a)) ω =
      ExceptionalTimes.rescaleTime a (C.trajectory hf ω) := by
  funext t
  exact retime_trajectory C ht hf (OrderIso.mulLeft₀ a ha) (mul_zero a) ω t

theorem exceptionalDimension_speedup (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (a : ℝ) (ha : 0 < a) (ω : Configuration)
    (d : ℝ≥0∞) (hd : ExceptionalDimension (C.trajectory hf ω) d) :
    ExceptionalDimension ((C.speedup a ha).trajectory
      (hf.retime (OrderIso.mulLeft₀ a ha) (mul_zero a)) ω) d := by
  rw [speedup_trajectory C ht hf]
  exact hd.rescaleTime ha

end ClockField
end ExceptionalTimes

#print axioms ExceptionalTimes.ClockField.BackwardTrace.retime
#print axioms ExceptionalTimes.ClockField.speedup_trajectory
#print axioms ExceptionalTimes.ClockField.exceptionalDimension_speedup
