import ExceptionalTimes.FiniteClockSlices

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ExceptionalTimes.FiniteClockSlicePath

open FiniteClockBridge FiniteClockSlices

def NoMarksBetween (C : ClockField) (a b : ℝ) : Prop :=
  ∀ u v t, C.Rings u v t → a < t → t ≤ b → False

theorem noMarks_colors (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (η : Configuration) {a b : ℝ}
    (hab : a ≤ b) (hn : NoMarksBetween C a b) :
    C.trajectory hf η b = C.trajectory hf η a := by
  funext v
  apply congrArg η
  apply ClockField.ancestor_eq_of_cutoffsAgree ht hf
  intro w t hr
  change t ≤ b ↔ t ≤ a
  constructor
  · intro hb
    by_contra ha
    exact hn v w t hr (lt_of_not_ge ha) hb
  · exact fun ha => ha.trans hab

theorem singleMark_colors (C : ClockField) (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (η : Configuration) {a b r : ℝ} {x y : Site}
    (har : a < r) (hrb : r ≤ b) (hr : C.Rings x y r)
    (honly : ∀ u v s, C.Rings u v s → a < s → s ≤ b →
      s = r ∧ s(u, v) = s(x, y)) :
    C.trajectory hf η b = C.trajectory hf η a ∘ Equiv.swap x y := by
  have hpre (v : Site) : C.CutoffsAgree v (TimeCutoff.before r) (TimeCutoff.closedAt a) := by
    intro w s hs
    change s < r ↔ s ≤ a
    constructor
    · intro hsr
      by_contra hsa
      exact hsr.ne (honly v w s hs (lt_of_not_ge hsa) (hsr.le.trans hrb)).1
    · exact fun hsa => hsa.trans_lt har
  have hlatest : ∀ u v, C.Rings u v r → C.LatestRing (TimeCutoff.closedAt b) u r v := by
    intro u v huv
    refine ⟨huv, hrb, ?_⟩
    intro z s hs hsb
    by_cases has : a < s
    · exact ((honly u z s hs has hsb).1).le
    · exact (le_of_not_gt has).trans har.le
  funext v
  by_cases hx : v = x
  · subst v
    change η (C.ancestor hf (TimeCutoff.closedAt b) x) =
      η (C.ancestor hf (TimeCutoff.closedAt a) (Equiv.swap x y x))
    rw [Equiv.swap_apply_left, ClockField.ancestor_eq_at_latest ht hf (hlatest x y hr),
      ClockField.ancestor_eq_of_cutoffsAgree ht hf (hpre y)]
  · by_cases hy : v = y
    · subst v
      change η (C.ancestor hf (TimeCutoff.closedAt b) y) =
        η (C.ancestor hf (TimeCutoff.closedAt a) (Equiv.swap x y y))
      rw [Equiv.swap_apply_right, ClockField.ancestor_eq_at_latest ht hf (hlatest y x hr.symm),
        ClockField.ancestor_eq_of_cutoffsAgree ht hf (hpre x)]
    · change η (C.ancestor hf (TimeCutoff.closedAt b) v) =
        η (C.ancestor hf (TimeCutoff.closedAt a) (Equiv.swap x y v))
      rw [Equiv.swap_apply_of_ne_of_ne hx hy]
      apply congrArg η
      apply ClockField.ancestor_eq_of_cutoffsAgree ht hf
      intro w s hs
      change s ≤ b ↔ s ≤ a
      constructor
      · intro hsb
        by_contra hsa
        have hp := (honly v w s hs (lt_of_not_ge hsa) hsb).2
        have hv : v ∈ s(x, y) := hp ▸ Sym2.mem_mk_left v w
        exact (Sym2.mem_iff.mp hv).elim hx hy
      · exact fun hsa => hsa.trans (har.le.trans hrb)

variable {I : Type*} [Fintype I] [DecidableEq I]

def pairIndex (edge : I → Site × Site) (i : I) : Sym2 Site := s((edge i).1, (edge i).2)

noncomputable def sliceCounts (C : ClockField) (edge : I → Site × Site) (a b : ℝ) : I → ℕ :=
  fun i => C.markCount (pairIndex edge i) a b

noncomputable def countUpdate (edge : I → Site × Site) (n : I → ℕ)
    (η : Configuration) : Configuration :=
  if hn : ∃ i, n = Pi.single i 1 then
    η ∘ Equiv.swap (edge hn.choose).1 (edge hn.choose).2
  else η

theorem countUpdate_single (edge : I → Site × Site) (i : I) (η : Configuration) :
    countUpdate edge (Pi.single i 1) η = η ∘ Equiv.swap (edge i).1 (edge i).2 := by
  have hex : ∃ j, (Pi.single i 1 : I → ℕ) = Pi.single j 1 := ⟨i, rfl⟩
  have hi : hex.choose = i := (single_injective hex.choose_spec).symm
  simp only [countUpdate, dite_eq_left hex, hi]

theorem countUpdate_zero (edge : I → Site × Site) (η : Configuration) :
    countUpdate edge 0 η = η := by
  have hn : ¬∃ i, (0 : I → ℕ) = Pi.single i 1 := by
    rintro ⟨i, hi⟩
    have := congrFun hi i
    simp at this
  simp only [countUpdate, dite_eq_right hn]

omit [Fintype I] [DecidableEq I] in
theorem noMarks_of_zero_counts (C : ClockField) (hc : C.FiniteEdgeCounts)
    (edge : I → Site × Site)
    (hsupport : ∀ u v t, C.Rings u v t → ∃ i, s(u, v) = pairIndex edge i)
    {a b : ℝ} (ha : 0 ≤ a) (hzero : sliceCounts C edge a b = 0) :
    NoMarksBetween C a b := by
  intro u v t hr hat htb
  obtain ⟨i, hi⟩ := hsupport u v t hr
  have hc0 := congrFun hzero i
  have hfin : (C.marks (pairIndex edge i) ∩ Set.Ioc a b).Finite :=
    (hc _ b).subset (fun s hs => ⟨hs.1, lt_of_le_of_lt ha hs.2.1, hs.2.2⟩)
  change (C.marks (pairIndex edge i) ∩ Set.Ioc a b).ncard = 0 at hc0
  have hempty := (Set.ncard_eq_zero hfin).mp hc0
  have hmem : t ∈ C.marks (pairIndex edge i) ∩ Set.Ioc a b := ⟨hi ▸ hr, hat, htb⟩
  rwa [hempty] at hmem

omit [Fintype I] in
theorem singleMark_of_single_counts (C : ClockField) (hc : C.FiniteEdgeCounts)
    (edge : I → Site × Site)
    (hsupport : ∀ u v t, C.Rings u v t → ∃ i, s(u, v) = pairIndex edge i)
    {a b : ℝ} (ha : 0 ≤ a) (i : I) (hone : sliceCounts C edge a b = Pi.single i 1) :
    ∃ t, a < t ∧ t ≤ b ∧ C.Rings (edge i).1 (edge i).2 t ∧
      ∀ u v s, C.Rings u v s → a < s → s ≤ b →
        s = t ∧ s(u, v) = pairIndex edge i := by
  have hci := congrFun hone i
  change C.markCount (pairIndex edge i) a b = (Pi.single i 1 : I → ℕ) i at hci
  rw [Pi.single_eq_same] at hci
  obtain ⟨t, ht⟩ := Set.ncard_eq_one.mp hci
  have hmem : t ∈ C.marks (pairIndex edge i) ∩ Set.Ioc a b := by rw [ht]; simp
  refine ⟨t, hmem.2.1, hmem.2.2, hmem.1, ?_⟩
  intro u v s hr has hsb
  obtain ⟨j, hj⟩ := hsupport u v s hr
  by_cases hji : j = i
  · subst j
    have hs : s ∈ C.marks (pairIndex edge i) ∩ Set.Ioc a b := ⟨hj ▸ hr, has, hsb⟩
    rw [ht] at hs
    exact ⟨Set.mem_singleton_iff.mp hs, hj⟩
  · have hcj := congrFun hone j
    change (C.marks (pairIndex edge j) ∩ Set.Ioc a b).ncard =
      (Pi.single i 1 : I → ℕ) j at hcj
    rw [Pi.single_eq_of_ne hji] at hcj
    have hfin : (C.marks (pairIndex edge j) ∩ Set.Ioc a b).Finite :=
      (hc _ b).subset (fun r hr => ⟨hr.1, lt_of_le_of_lt ha hr.2.1, hr.2.2⟩)
    have hempty := (Set.ncard_eq_zero hfin).mp hcj
    have hs : s ∈ C.marks (pairIndex edge j) ∩ Set.Ioc a b := ⟨hj ▸ hr, has, hsb⟩
    rw [hempty] at hs
    exact hs.elim

theorem goodSlice_colors (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    (edge : I → Site × Site)
    (hsupport : ∀ u v t, C.Rings u v t → ∃ i, s(u, v) = pairIndex edge i)
    (η : Configuration) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hgood : GoodCounts (sliceCounts C edge a b)) :
    C.trajectory hf η b = countUpdate edge (sliceCounts C edge a b) (C.trajectory hf η a) := by
  rcases hgood with hz | ⟨i, hi⟩
  · rw [hz, countUpdate_zero]
    exact noMarks_colors C ht hf η hab (noMarks_of_zero_counts C hc edge hsupport ha hz)
  · rw [hi, countUpdate_single]
    obtain ⟨t, hat, htb, hring, honly⟩ := singleMark_of_single_counts C hc edge hsupport ha i hi
    exact singleMark_colors C ht hf η hat htb hring honly

noncomputable def runGrid (C : ClockField) (edge : I → Site × Site) (h : ℝ)
    (η : Configuration) : ℕ → Configuration
  | 0 => η
  | n + 1 => countUpdate edge (sliceCounts C edge ((n : ℝ) * h) (((n : ℝ) + 1) * h))
      (runGrid C edge h η n)

theorem trajectory_eq_runGrid_of_good (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    (edge : I → Site × Site)
    (hsupport : ∀ u v t, C.Rings u v t → ∃ i, s(u, v) = pairIndex edge i)
    (η : Configuration) (h : ℝ) (hh : 0 ≤ h) (n : ℕ)
    (hgood : ∀ j < n, GoodCounts (sliceCounts C edge ((j : ℝ) * h) (((j : ℝ) + 1) * h))) :
    C.trajectory hf η ((n : ℝ) * h) = runGrid C edge h η n := by
  induction n with
  | zero => simpa [runGrid] using ClockField.trajectory_zero ht hf η
  | succ n ih =>
    have hstep := goodSlice_colors C hc ht hf edge hsupport η
      (mul_nonneg (Nat.cast_nonneg n) hh)
      (show (n : ℝ) * h ≤ ((n : ℝ) + 1) * h by nlinarith)
      (hgood n (Nat.lt_succ_self n))
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by simp, hstep, runGrid,
      ih (fun j hj => hgood j (Nat.lt_succ_of_lt hj))]

#print axioms trajectory_eq_runGrid_of_good

end ExceptionalTimes.FiniteClockSlicePath
