import ExceptionalTimes.ClockTruncation
import ExceptionalTimes.TimeClosure

/-! Literal one-sided local constancy of transported colors. The left
statement follows already from finite strict backward traces; the right
statement needs local finiteness of incident marks. -/

open scoped Classical
open Set Filter
open scoped Topology

namespace ExceptionalTimes.ClockPathRegularity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_last_bound_before (C : ClockField) (hf : C.HasFiniteBackwardTraces)
    (v : Site) (t : ℝ) :
    ∃ a < t, ∀ w s, C.Rings v w s → s < t → s ≤ a := by
  obtain ⟨x,hx⟩ := hf (TimeCutoff.before t) v
  cases hx with
  | stop h => exact ⟨t-1,by linarith,fun w s hs hst => (h w s hs hst).elim⟩
  | @jump c v r w origin h tail => exact ⟨r,h.allowed,fun z s hs hst => h.latest z s hs hst⟩

/-- The strict-cutoff coloring is exactly the local left limit at each
site, with an actual interval of constancy. -/
theorem left_locally_constant (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (η : Configuration) (v : Site) (t : ℝ) :
    ∃ a < t, ∀ s, a ≤ s → s < t →
      C.trajectory hf η s v = C.leftConfiguration hf η t v := by
  obtain ⟨a,hat,ha⟩ := exists_last_bound_before C hf v t
  refine ⟨a,hat,?_⟩
  intro s has hst
  apply congrArg η
  apply ClockField.ancestor_eq_of_cutoffsAgree ht hf
  intro w r hr
  change r ≤ s ↔ r < t
  exact ⟨fun hrs => hrs.trans_lt hst,fun hrt => (ha w r hr hrt).trans has⟩

/-- Locally finite incident marks also give an actual interval of right
constancy, including the color at its left endpoint. -/
theorem right_locally_constant (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (hloc : C.LocallyFiniteIncident)
    (η : Configuration) (v : Site) (t : ℝ) :
    ∃ b > t, ∀ s, t ≤ s → s ≤ b → C.trajectory hf η s v = C.trajectory hf η t v := by
  let S := (hloc v (t+1)).toFinset.image Prod.fst
  let U := insert (t+1) (S.filter (fun r => t < r))
  have hUne : U.Nonempty := ⟨t+1,Finset.mem_insert_self _ _⟩
  have hgt : ∀ r ∈ U, t < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · linarith
    · exact (Finset.mem_filter.mp hr).2
  have htmin := hgt _ (U.min'_mem hUne)
  let b := (t+U.min' hUne)/2
  have htb : t < b := by dsimp [b]; linarith
  have hbmin : b < U.min' hUne := by dsimp [b]; linarith
  have hb1 : b < t+1 := hbmin.trans_le (U.min'_le _ (Finset.mem_insert_self _ _))
  refine ⟨b,htb,?_⟩
  intro s hts hsb
  apply congrArg η
  apply ClockField.ancestor_eq_of_cutoffsAgree ht hf
  intro w r hr
  change r ≤ s ↔ r ≤ t
  constructor
  · intro hrs
    by_contra! htr
    have hrS : r ∈ S := Finset.mem_image.mpr
      ⟨(r,w),(hloc v (t+1)).mem_toFinset.mpr ⟨hr,(hrs.trans hsb).trans hb1.le⟩,rfl⟩
    have hrU : r ∈ U := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hrS,htr⟩)
    have hmin := U.min'_le _ hrU
    exact (not_lt_of_ge (hrs.trans hsb)) (hbmin.trans_le hmin)
  · exact fun hrt => hrt.trans hts

/-- Closing black-time sets can change a site only at an actual incident
ring time. This is a deterministic statement, not the percolation
preservation assertion of GV Lemma 2.2. -/
theorem closedColors_eq_without_mark (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (hloc : C.LocallyFiniteIncident)
    (η : Configuration) (v : Site) (t : ℝ) (ht0 : 0 ≤ t)
    (hno : ∀ w, ¬ C.Rings v w t) :
    TimeClosure.closedColors (C.trajectory hf η) t v = C.trajectory hf η t v := by
  obtain ⟨a,hat,ha⟩ := left_locally_constant C ht hf η v t
  obtain ⟨b,htb,hb⟩ := right_locally_constant C ht hf hloc η v t
  have he := ClockField.trajectory_unchanged_without_mark ht hf η hno
  have hconst : ∀ s ∈ Ioo a b, C.trajectory hf η s v = C.trajectory hf η t v := by
    intro s hs
    by_cases hst : s < t
    · exact (ha s hs.1.le hst).trans he.symm
    · exact hb s (le_of_not_gt hst) hs.2.le
  apply Bool.eq_iff_iff.mpr
  rw [TimeClosure.closedColors_eq_true]
  constructor
  · intro hclosed
    obtain ⟨s,hs,hnear⟩ := ((mem_closure_iff_frequently.mp hclosed).and_eventually
      (Ioo_mem_nhds hat htb)).exists
    exact (hconst s hnear) ▸ hs.2
  · intro hblack
    exact subset_closure ⟨ht0,hblack⟩

/-- At a time when exactly one edge rings, all possible changes made by
site-time closure are confined to that edge's two endpoints. -/
theorem closedColors_eq_outside_ring (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (hloc : C.LocallyFiniteIncident)
    (η : Configuration) {u w t} (hring : C.Rings u w t)
    (hglobal : ∀ e f s, s ∈ C.marks e → s ∈ C.marks f → e = f)
    (v : Site) (hvu : v ≠ u) (hvw : v ≠ w) :
    TimeClosure.closedColors (C.trajectory hf η) t v = C.trajectory hf η t v := by
  apply closedColors_eq_without_mark C ht hf hloc η v t hring.pos.le
  intro x hx
  have hp : s(v,x) = s(u,w) := hglobal _ _ _ hx hring
  have hv : v ∈ s(u,w) := hp ▸ Sym2.mem_mk_left v x
  exact (Sym2.mem_iff.mp hv).elim hvu hvw

#print axioms left_locally_constant
#print axioms right_locally_constant
#print axioms closedColors_eq_without_mark
#print axioms closedColors_eq_outside_ring

end ExceptionalTimes.ClockPathRegularity
