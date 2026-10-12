import ExceptionalTimes.FiniteEdgeEnumeration

open scoped Classical

namespace ExceptionalTimes.FiniteEdgeExhaustion

/-- A deterministic monotone exhaustion exists for every countable index set.
It does not depend on the sampled clocks or the observation window. -/
theorem exists_finset_exhaustion (E : Type*) [Countable E] [Nonempty E] [DecidableEq E] :
    ∃ F : ℕ → Finset E, Monotone F ∧ ∀ e, ∃ n, e ∈ F n := by
  obtain ⟨f, hf⟩ := (countable_iff_exists_surjective (α := E)).mp inferInstance
  refine ⟨fun n => (Finset.range n).image f, ?_, ?_⟩
  · intro m n hmn
    exact Finset.image_subset_image (Finset.range_mono hmn)
  · intro e
    obtain ⟨n, rfl⟩ := hf e
    exact ⟨n + 1, Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩⟩

noncomputable def edges : ℕ → Finset (Sym2 Site) :=
  Classical.choose (exists_finset_exhaustion (Sym2 Site))

theorem edges_monotone : Monotone edges :=
  (Classical.choose_spec (exists_finset_exhaustion (Sym2 Site))).1

theorem edges_exhaustive : ∀ e, ∃ n, e ∈ edges n :=
  (Classical.choose_spec (exists_finset_exhaustion (Sym2 Site))).2

#print axioms edges_exhaustive

end ExceptionalTimes.FiniteEdgeExhaustion
