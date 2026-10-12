import ExceptionalTimes.GraphicalProcess

/-! The backward construction in GV Appendix A starts with a closed time
cutoff. Its existence at every nonnegative time already gives every strict
cutoff required by the concrete clock model, without a further regularity
assumption. At a ring, inspect the closed trace from the other endpoint. -/

namespace ExceptionalTimes.ClockField

def HasClosedBackwardTraces (C : ClockField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ v, ∃ a, C.BackwardTrace (TimeCutoff.closedAt t) v a

theorem closed_trace_all_real (C : ClockField) (h : C.HasClosedBackwardTraces)
    (t : ℝ) (v : Site) : ∃ a, C.BackwardTrace (TimeCutoff.closedAt t) v a := by
  by_cases ht : 0 ≤ t
  · exact h t ht v
  · refine ⟨v,.stop ?_⟩
    intro w s hs ha
    have hpos := hs.pos
    change s ≤ t at ha
    linarith

theorem before_trace_of_closed (C : ClockField) (hties : C.NoIncidentTies)
    (h : C.HasClosedBackwardTraces) (t : ℝ) (v : Site) :
    ∃ a, C.BackwardTrace (TimeCutoff.before t) v a := by
  by_cases hring : ∃ w, C.Rings v w t
  · obtain ⟨w,hring⟩ := hring
    obtain ⟨a,p⟩ := C.closed_trace_all_real h t w
    cases p with
    | stop hstop => exact (hstop v t hring.symm le_rfl).elim
    | @jump _ _ s y a hl tail =>
      have hst : s = t := le_antisymm hl.allowed (hl.latest v t hring.symm le_rfl)
      subst s
      have hyv : y = v := hties w y v t hl.rings hring.symm
      subst y
      exact ⟨a,tail⟩
  · obtain ⟨a,p⟩ := C.closed_trace_all_real h t v
    refine ⟨a,p.changeCutoff ?_⟩
    intro w s hs
    change s ≤ t ↔ s < t
    refine ⟨fun hst => lt_of_le_of_ne hst ?_,fun hst => hst.le⟩
    intro heq
    subst s
    exact hring ⟨w,hs⟩

theorem hasFiniteBackwardTraces_of_closed (C : ClockField) (hties : C.NoIncidentTies)
    (h : C.HasClosedBackwardTraces) : C.HasFiniteBackwardTraces := by
  rintro ⟨t,closed⟩ v
  cases closed with
  | false => exact C.before_trace_of_closed hties h t v
  | true => exact C.closed_trace_all_real h t v

#print axioms hasFiniteBackwardTraces_of_closed

end ExceptionalTimes.ClockField
