import ExceptionalTimes.ManyDimerLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
Regrouping the genuine product dimer environment into mesoscopic cells.
The variance estimate must sum over those cells, rather than over individual
dimers. All reindexings here are proved for literal normalized finite laws.
The only variance premise is the classical Efron--Stein inequality for the
grouped independent environments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical

namespace ExceptionalTimes.GroupedDimerLaw

noncomputable section

open EnvironmentVariance

variable {I : Type*} [Fintype I]
variable {J : I → Type*} [∀ i, Fintype (J i)]

local instance : DecidableEq (Sigma J) := fun a b => Classical.propDecidable (a = b)

def flatten {A : (i : I) → J i → Type*} (x : ∀ i j, A i j) :
    (s : Sigma J) → A s.1 s.2 := fun s => x s.1 s.2

def curry {A : (i : I) → J i → Type*} (x : (s : Sigma J) → A s.1 s.2) :
    ∀ i j, A i j := fun i j => x ⟨i, j⟩

def flattenEquiv (A : (i : I) → J i → Type*) :
    (∀ i j, A i j) ≃ ((s : Sigma J) → A s.1 s.2) where
  toFun := flatten
  invFun := curry
  left_inv _ := rfl
  right_inv _ := rfl

theorem expect_pi_nested {A : (i : I) → J i → Type*}
    [∀ i j, Fintype (A i j)] (μ : ∀ i j, FiniteLaw (A i j))
    (f : ((s : Sigma J) → A s.1 s.2) → ℝ) :
    (FiniteLaw.pi (fun s : Sigma J => μ s.1 s.2)).expect f =
      (FiniteLaw.pi (fun i => FiniteLaw.pi (μ i))).expect (fun x => f (flatten x)) := by
  classical
  unfold FiniteLaw.expect
  rw [← (flattenEquiv A).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ s : Sigma J, (μ s.1 s.2).weight (x s.1 s.2)) * f (flatten x) =
    (∏ i, ∏ j, (μ i j).weight (x i j)) * f (flatten x)
  rw [Fintype.prod_sigma]

variable {A S : (i : I) → J i → Type*}
variable [∀ i j, Fintype (A i j)] [∀ i j, Fintype (S i j)]

theorem paired_nested (ρ : ∀ i j, FiniteLaw (A i j))
    (K : ∀ i j, A i j → FiniteLaw (S i j))
    (E : ((s : Sigma J) → S s.1 s.2) → Prop) :
    pairedProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
      (cellKernel (fun s : Sigma J => K s.1 s.2)) E =
    pairedProbability (FiniteLaw.pi (fun i => FiniteLaw.pi (ρ i)))
      (cellKernel (fun i e => cellKernel (K i) e)) (fun x => E (flatten x)) := by
  unfold pairedProbability cellKernel
  rw [expect_pi_nested]
  apply FiniteLaw.expect_congr
  intro e
  change (FiniteLaw.pi (fun s : Sigma J => K s.1 s.2 (e s.1 s.2))).expect _ = _
  rw [expect_pi_nested (fun i j => K i j (e i j))]
  apply FiniteLaw.expect_congr
  intro x
  exact expect_pi_nested (fun i j => K i j (e i j)) _

theorem marginal_nested (ρ : ∀ i j, FiniteLaw (A i j))
    (K : ∀ i j, A i j → FiniteLaw (S i j))
    (E : ((s : Sigma J) → S s.1 s.2) → Prop) :
    marginalProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
      (cellKernel (fun s : Sigma J => K s.1 s.2)) E =
    marginalProbability (FiniteLaw.pi (fun i => FiniteLaw.pi (ρ i)))
      (cellKernel (fun i e => cellKernel (K i) e)) (fun x => E (flatten x)) := by
  unfold marginalProbability probability cellKernel
  rw [expect_pi_nested]
  apply FiniteLaw.expect_congr
  intro e
  exact expect_pi_nested (fun i j => K i j (e i j)) _

/-- Arbitrary-assignment pivotality of a whole group. This permits changing
every dimer in group i, while all colors in the other groups remain fixed. -/
def GroupPivotal (E : ((s : Sigma J) → S s.1 s.2) → Prop) (i : I)
    (x : (s : Sigma J) → S s.1 s.2) : Prop :=
  CellPivotal (fun y => E (flatten y)) i (curry x)

/-- Replace all colors in one group and preserve the other groups. -/
def replaceGroup (x : (s : Sigma J) → S s.1 s.2) (i : I) (a : ∀ j, S i j) :
    (s : Sigma J) → S s.1 s.2 := flatten (Function.update (curry x) i a)

omit [Fintype I] [∀ i, Fintype (J i)] [∀ i j, Fintype (S i j)] in
theorem replaceGroup_outside (x : (s : Sigma J) → S s.1 s.2) (i : I)
    (a : ∀ j, S i j) (s : Sigma J) (hs : s.1 ≠ i) :
    replaceGroup x i a s = x s := by
  simp [replaceGroup, flatten, curry, Function.update_of_ne hs]

omit [Fintype I] [∀ i, Fintype (J i)] [∀ i j, Fintype (S i j)] in
theorem groupPivotal_iff_replace
    (E : ((s : Sigma J) → S s.1 s.2) → Prop) (i : I)
    (x : (s : Sigma J) → S s.1 s.2) :
    GroupPivotal E i x ↔ ∃ a b, ¬ (E (replaceGroup x i a) ↔ E (replaceGroup x i b)) := by
  have hs (a : ∀ j, S i j) :
      (Equiv.piSplitAt i (fun k => ∀ j, S k j)).symm
        (a, ((Equiv.piSplitAt i (fun k => ∀ j, S k j)) (curry x)).2) =
      Function.update (curry x) i a := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Equiv.piSplitAt]
    · simp [Equiv.piSplitAt, hk]
  simp only [GroupPivotal, CellPivotal, Pivotal, cellEvent, hs, replaceGroup]

omit [Fintype I] [∀ i, Fintype (J i)] [∀ i j, Fintype (S i j)] in
/-- Equivalent description using arbitrary full assignments with exactly the
original exterior. The choices inside the group need not be dynamic updates. -/
theorem groupPivotal_iff_outside
    (E : ((s : Sigma J) → S s.1 s.2) → Prop) (i : I)
    (x : (s : Sigma J) → S s.1 s.2) :
    GroupPivotal E i x ↔ ∃ y z : (s : Sigma J) → S s.1 s.2,
      (∀ s, s.1 ≠ i → y s = x s ∧ z s = x s) ∧ ¬ (E y ↔ E z) := by
  rw [groupPivotal_iff_replace]
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨replaceGroup x i a, replaceGroup x i b,
      fun s hs => ⟨replaceGroup_outside x i a s hs, replaceGroup_outside x i b s hs⟩, hab⟩
  · rintro ⟨y, z, hout, hne⟩
    refine ⟨fun j => y ⟨i, j⟩, fun j => z ⟨i, j⟩, ?_⟩
    have hrep (u : (s : Sigma J) → S s.1 s.2)
        (hu : ∀ s, s.1 ≠ i → u s = x s) :
        replaceGroup x i (fun j => u ⟨i, j⟩) = u := by
      funext s
      rcases s with ⟨k, j⟩
      by_cases hk : k = i
      · subst k
        simp [replaceGroup, flatten]
      · rw [replaceGroup_outside _ _ _ _ hk]
        exact (hu ⟨k, j⟩ hk).symm
    simpa only [hrep y (fun s hs => (hout s hs).1),
      hrep z (fun s hs => (hout s hs).2)] using hne

theorem grouped_variance (ρ : ∀ i j, FiniteLaw (A i j))
    (K : ∀ i j, A i j → FiniteLaw (S i j))
    (E : ((s : Sigma J) → S s.1 s.2) → Prop)
    (hES : EfronStein (fun i => FiniteLaw.pi (ρ i))) :
    pairedProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
        (cellKernel (fun s : Sigma J => K s.1 s.2)) E -
      marginalProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
        (cellKernel (fun s : Sigma J => K s.1 s.2)) E ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i,
        pairedProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
          (cellKernel (fun s : Sigma J => K s.1 s.2)) (GroupPivotal E i) := by
  simp only [paired_nested, marginal_nested, GroupPivotal]
  exact grouped_environment_variance (fun i => FiniteLaw.pi (ρ i))
    (fun i e => cellKernel (K i) e) (fun x => E (flatten x)) hES

open DimerLaw ManyDimerLaw FiniteHaar

/-- The actual canonical dimer law satisfies the mesoscopic-cell variance
bound. Groups may have different finite sizes. -/
theorem grouped_dimer_variance
    (p : Sigma J → ℝ) (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (E : (Sigma J → Color) → Prop)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun j => environmentLaw (p ⟨i,j⟩) (hp0 ⟨i,j⟩) (hp1 ⟨i,j⟩)))) :
    manyProbability p E - (average (fun x => indicator (E x))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i,
        manyProbability p (GroupPivotal (S := fun _ _ => Color) E i) := by
  have hm := (many_marginal_probability p hp0 hp1 E).trans
    (average_congr_instances _ (inferInstance : Fintype (Sigma J → Color))
      _ (fun x => indicator (E x)) (fun _ => rfl))
  rw [← hm]
  simp_rw [manyProbability_eq_paired p hp0 hp1]
  exact grouped_variance
    (fun i j => environmentLaw (p ⟨i,j⟩) (hp0 ⟨i,j⟩) (hp1 ⟨i,j⟩))
    (fun _ _ => replicaLaw) E hES

end

end ExceptionalTimes.GroupedDimerLaw

#print axioms ExceptionalTimes.GroupedDimerLaw.grouped_variance
#print axioms ExceptionalTimes.GroupedDimerLaw.grouped_dimer_variance
#print axioms ExceptionalTimes.GroupedDimerLaw.groupPivotal_iff_outside
