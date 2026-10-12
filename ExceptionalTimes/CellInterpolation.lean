import ExceptionalTimes.Model

/-!
# From an arbitrary pivotal cell to a single-site pivot

The interpolation changes only sites of the given finite cell. The
intermediate coloring need not preserve canonical block counts: it is a
deterministic witness for arbitrary-assignment pivotality, not a proposed
dynamical transition. No planar arm or Jordan conclusion is assumed here.
-/

namespace ExceptionalTimes
namespace CellInterpolation

/-- Two assignments inside `D`, keeping its exterior fixed, can change `F`. -/
def CellPivotal (F : Configuration → Bool) (D : Finset Site)
    (ω : Configuration) : Prop :=
  ∃ a b : Configuration,
    (∀ w, w ∉ D → a w = ω w) ∧
    (∀ w, w ∉ D → b w = ω w) ∧ F a ≠ F b

/-- Interpolate by single-coordinate updates until the first change in `F`.
The chosen coordinate still has its initial value, every intermediate value
is one of the two endpoint values, and `F` retains its initial value. -/
theorem first_changed_update (F : Configuration → Bool) (D : Finset Site)
    (a b : Configuration) (hab : ∀ w, w ∉ D → a w = b w)
    (hF : F a ≠ F b) :
    ∃ η v, v ∈ D ∧ η v = a v ∧
      (∀ w, w ∉ D → η w = a w) ∧
      (∀ w, η w = a w ∨ η w = b w) ∧
      F η = F a ∧ F (Function.update η v (b v)) ≠ F η := by
  classical
  induction D using Finset.induction_on generalizing a with
  | empty =>
      have heq : a = b := funext fun w => hab w (by simp)
      exact (hF (congrArg F heq)).elim
  | @insert v D hv ih =>
      let a' : Configuration := Function.update a v (b v)
      by_cases hstep : F a' = F a
      · have hab' : ∀ w, w ∉ D → a' w = b w := by
          intro w hw
          by_cases hwv : w = v
          · simp [a', hwv]
          · simpa [a', hwv] using hab w (by simp [hw, hwv])
        have hF' : F a' ≠ F b := by rwa [hstep]
        obtain ⟨η, w, hwD, hηw, hext, hvalues, hηF, hpiv⟩ := ih a' hab' hF'
        have hwv : w ≠ v := fun h => hv (h ▸ hwD)
        refine ⟨η, w, Finset.mem_insert_of_mem hwD, ?_, ?_, ?_,
          hηF.trans hstep, hpiv⟩
        · simpa [a', hwv] using hηw
        · intro z hz
          have hzD : z ∉ D := fun h => hz (Finset.mem_insert_of_mem h)
          have hzv : z ≠ v := fun h => hz (by simp [h])
          simpa [a', hzv] using hext z hzD
        · intro z
          rcases hvalues z with hz | hz
          · by_cases hzv : z = v
            · exact Or.inr (by simpa [a', hzv] using hz)
            · exact Or.inl (by simpa [a', hzv] using hz)
          · exact Or.inr hz
      · exact ⟨a, v, by simp, rfl, fun _ _ => rfl,
          fun _ => Or.inl rfl, rfl, hstep⟩

/-- A value-changing Boolean update is the literal flip at that site. -/
theorem changed_update_is_flip (F : Configuration → Bool)
    (η : Configuration) (v : Site) (c : Bool)
    (h : F (Function.update η v c) ≠ F η) :
    F (Function.update η v (!(η v))) ≠ F η := by
  have hne : c ≠ η v := by
    intro hc
    rw [hc, Function.update_eq_self] at h
    exact h rfl
  have hc : c = !(η v) := by
    cases hη : η v <;> cases c <;> simp_all
  rwa [← hc]

/-- The actual finite-cell reduction: a single-site flip in a coloring that
agrees with the original coloring everywhere outside the cell. -/
theorem cell_pivotal_single_site (F : Configuration → Bool) (D : Finset Site)
    (ω : Configuration) (h : CellPivotal F D ω) :
    ∃ η v, v ∈ D ∧ (∀ w, w ∉ D → η w = ω w) ∧
      F (Function.update η v (!(η v))) ≠ F η := by
  obtain ⟨a, b, ha, hb, hF⟩ := h
  have hab : ∀ w, w ∉ D → a w = b w :=
    fun w hw => (ha w hw).trans (hb w hw).symm
  obtain ⟨η, v, hv, _, hext, _, _, hpiv⟩ := first_changed_update F D a b hab hF
  exact ⟨η, v, hv, fun w hw => (hext w hw).trans (ha w hw),
    changed_update_is_flip F η v (b v) hpiv⟩

/-- Both black/white single-site completions have the same fixed exterior,
and differ in the event value. This is the input for planar separation. -/
theorem cell_pivotal_black_white (F : Configuration → Bool) (D : Finset Site)
    (ω : Configuration) (h : CellPivotal F D ω) :
    ∃ η v, v ∈ D ∧
      (∀ c : Bool, ∀ w, w ∉ D → Function.update η v c w = ω w) ∧
      F (Function.update η v true) ≠ F (Function.update η v false) := by
  obtain ⟨η, v, hv, hext, hpiv⟩ := cell_pivotal_single_site F D ω h
  refine ⟨η, v, hv, ?_, ?_⟩
  · intro c w hw
    have hwv : w ≠ v := fun h => hw (h ▸ hv)
    simpa [hwv] using hext w hw
  · cases hc : η v
    · have hfalse : Function.update η v false = η := by simp [← hc]
      simpa [hc, hfalse] using hpiv
    · have htrue : Function.update η v true = η := by simp [← hc]
      exact Ne.symm (by simpa [hc, htrue] using hpiv)

/-- For an increasing Boolean event, the two completions have the expected
orientation: black makes the event true and white makes it false. -/
theorem monotone_cell_pivotal_black_white (F : Configuration → Bool)
    (hmono : Monotone F) (D : Finset Site) (ω : Configuration)
    (h : CellPivotal F D ω) :
    ∃ η v, v ∈ D ∧
      (∀ c : Bool, ∀ w, w ∉ D → Function.update η v c w = ω w) ∧
      F (Function.update η v true) = true ∧
      F (Function.update η v false) = false := by
  obtain ⟨η, v, hv, hext, hne⟩ := cell_pivotal_black_white F D ω h
  have hupdate : Function.update η v false ≤ Function.update η v true := by
    intro w
    by_cases hw : w = v <;> simp [hw]
  have hle := hmono hupdate
  refine ⟨η, v, hv, hext, ?_⟩
  cases hblack : F (Function.update η v true) <;>
    cases hwhite : F (Function.update η v false) <;> simp_all
  exact (by decide : ¬ ((true : Bool) ≤ false)) hle

/-- Consequently, a black witness in one completion and a white witness in
the other can intersect only at the pivot. This does not assert the
existence, simplicity, winding, or arm order of either witness. -/
theorem opposite_completion_colors_intersect_only_at_pivot
    (η : Configuration) (v w : Site)
    (hb : Function.update η v true w = true)
    (hw : Function.update η v false w = false) : w = v := by
  by_contra hne
  simp [hne] at hb hw
  rw [hb] at hw
  cases hw

end CellInterpolation
end ExceptionalTimes

#print axioms ExceptionalTimes.CellInterpolation.first_changed_update
#print axioms ExceptionalTimes.CellInterpolation.cell_pivotal_single_site
#print axioms ExceptionalTimes.CellInterpolation.cell_pivotal_black_white
#print axioms ExceptionalTimes.CellInterpolation.monotone_cell_pivotal_black_white
