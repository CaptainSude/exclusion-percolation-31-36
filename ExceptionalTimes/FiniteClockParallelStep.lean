import ExceptionalTimes.FiniteClockShiftedGrid

/-! A count update that performs all disjoint simultaneous exchanges.
It is exact whenever a slice contains at most one distinct mark time;
there may be arbitrarily many disjoint edges ringing at that time. -/

open scoped Classical

namespace ExceptionalTimes.FiniteClockParallelStep

open FiniteClockBridge FiniteClockSlicePath FiniteClockWordLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type*}

def activeAt (edge : I → Site × Site) (c : I → ℕ) (v : Site) : Prop :=
  ∃ i, c i ≠ 0 ∧ (v = (edge i).1 ∨ v = (edge i).2)

noncomputable def countAncestor (edge : I → Site × Site) (c : I → ℕ) (v : Site) : Site :=
  if h : activeAt edge c v then
    Equiv.swap (edge h.choose).1 (edge h.choose).2 v else v

noncomputable def parallelUpdate (edge : I → Site × Site) (c : I → ℕ)
    (η : Configuration) : Configuration := η ∘ countAncestor edge c

theorem count_ne_zero_iff (C : ClockField) (hc : C.FiniteEdgeCounts)
    (e : Sym2 Site) {a b : ℝ} (ha : 0 ≤ a) :
    C.markCount e a b ≠ 0 ↔ ∃ t, t ∈ C.marks e ∧ a < t ∧ t ≤ b := by
  have hf : (C.marks e ∩ Set.Ioc a b).Finite :=
    (hc e b).subset (fun _ ht => ⟨ht.1,lt_of_le_of_lt ha ht.2.1,ht.2.2⟩)
  rw [ClockField.markCount,ne_eq,Set.ncard_eq_zero hf]
  exact Set.nonempty_iff_ne_empty.symm

/-- All marks in the slice share a common time; their edges may differ. -/
def OneTimeSlice (C : ClockField) (a b τ : ℝ) : Prop :=
  ∀ u v t, C.Rings u v t → a < t → t ≤ b → t = τ

theorem oneTimeSlice_colors (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    (edge : I → Site × Site)
    (hcover : ∀ u v t, C.Rings u v t → ∃ i, s(u,v) = pairIndex edge i)
    (η : Configuration) {a b τ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hone : OneTimeSlice C a b τ) :
    C.trajectory hf η b = parallelUpdate edge (sliceCounts C edge a b) (C.trajectory hf η a) := by
  funext v
  simp only [parallelUpdate,Function.comp_apply]
  unfold countAncestor
  split_ifs with hv
  · let i := hv.choose
    have hi : sliceCounts C edge a b i ≠ 0 ∧ (v = (edge i).1 ∨ v = (edge i).2) := hv.choose_spec
    obtain ⟨r,hr,har,hrb⟩ := (count_ne_zero_iff C hc (pairIndex edge i) ha).mp hi.1
    have hring : C.Rings (edge i).1 (edge i).2 r := hr
    have hrτ := hone _ _ _ hring har hrb
    have hvr : C.Rings v (Equiv.swap (edge i).1 (edge i).2 v) r := by
      rcases hi.2 with hv | hv
      · rw [hv,Equiv.swap_apply_left]
        exact hring
      · rw [hv,Equiv.swap_apply_right]
        exact hring.symm
    have hright : C.trajectory hf η b v = C.trajectory hf η r v := by
      apply congrArg η
      apply ClockField.ancestor_eq_of_cutoffsAgree ht hf
      intro w q hq
      change q ≤ b ↔ q ≤ r
      constructor
      · intro hqb
        by_cases hqa : q ≤ a
        · exact hqa.trans har.le
        · have hqτ := hone _ _ _ hq (lt_of_not_ge hqa) hqb
          exact le_of_eq (hqτ.trans hrτ.symm)
      · exact fun hqr => hqr.trans hrb
    have hleft : C.leftConfiguration hf η r (Equiv.swap (edge i).1 (edge i).2 v) =
        C.trajectory hf η a (Equiv.swap (edge i).1 (edge i).2 v) := by
      apply congrArg η
      apply ClockField.ancestor_eq_of_cutoffsAgree ht hf
      intro w q hq
      change q < r ↔ q ≤ a
      constructor
      · intro hqr
        by_contra! haq
        have hqτ := hone _ _ _ hq haq (hqr.le.trans hrb)
        exact (ne_of_lt hqr) (hqτ.trans hrτ.symm)
      · exact fun hqa => hqa.trans_lt har
    exact hright.trans ((ClockField.trajectory_at_mark ht hf η hvr).trans hleft)
  · apply congrArg η
    apply ClockField.ancestor_eq_of_cutoffsAgree ht hf
    intro w r hr
    change r ≤ b ↔ r ≤ a
    constructor
    · intro hrb
      by_contra! har
      obtain ⟨i,hi⟩ := hcover v w r hr
      apply hv
      refine ⟨i,?_,?_⟩
      · apply (count_ne_zero_iff C hc (pairIndex edge i) ha).mpr
        exact ⟨r,hi ▸ hr,har,hrb⟩
      · have hm : v ∈ pairIndex edge i := hi ▸ Sym2.mem_mk_left v w
        exact Sym2.mem_iff.mp hm
    · exact fun hra => hra.trans hab

theorem countAncestor_mem (V : Finset Site) (edge : I → V × V) (c : I → ℕ) (v : V) :
    countAncestor (siteEdges V edge) c v ∈ V := by
  unfold countAncestor
  split_ifs with h
  · let i := h.choose
    change Equiv.swap (siteEdges V edge i).1 (siteEdges V edge i).2 (v : Site) ∈ V
    have hi : (v : Site) = (siteEdges V edge i).1 ∨ (v : Site) = (siteEdges V edge i).2 := h.choose_spec.2
    rcases hi with hv | hv
    · rw [hv,Equiv.swap_apply_left]
      exact (edge i).2.property
    · rw [hv,Equiv.swap_apply_right]
      exact (edge i).1.property
  · exact v.property

noncomputable def parallelCubeUpdate (V : Finset Site) (edge : I → V × V)
    (c : I → ℕ) (ξ : V → Bool) : V → Bool :=
  fun v => ξ ⟨countAncestor (siteEdges V edge) c v,countAncestor_mem V edge c v⟩

theorem restrict_parallelUpdate (V : Finset Site) (edge : I → V × V)
    (c : I → ℕ) (η : Configuration) :
    restrictColor V (parallelUpdate (siteEdges V edge) c η) =
      parallelCubeUpdate V edge c (restrictColor V η) := rfl

theorem restrict_parallelWord (V : Finset Site) (edge : I → V × V)
    (n : ℕ) (w : Fin n → I → ℕ) (η : Configuration) :
    restrictColor V (runWord (parallelUpdate (siteEdges V edge)) w η) =
      runWord (parallelCubeUpdate V edge) w (restrictColor V η) := by
  induction n generalizing η with
  | zero => rfl
  | succ n ih =>
    simp only [runWord]
    rw [ih,restrict_parallelUpdate]

#print axioms oneTimeSlice_colors
#print axioms restrict_parallelWord

end ExceptionalTimes.FiniteClockParallelStep
