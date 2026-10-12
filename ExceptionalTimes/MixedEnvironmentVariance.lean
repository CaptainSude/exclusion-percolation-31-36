import ExceptionalTimes.GroupedDimerLaw

/-! Grouped environment variance with a fresh independent exterior in each
replica. Only active cells have environment coordinates, hence only active
cells occur in the pivotal sum. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedEnvironmentVariance

open EnvironmentVariance

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
variable {A S : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (S i)]

def mixedKernel (K : ∀ i, A i → FiniteLaw (S i)) (μ : FiniteLaw O)
    (e : ∀ i, A i) : FiniteLaw ((∀ i, S i) × O) := (cellKernel K e).prod μ

def activePivotal (E : ((∀ i, S i) × O) → Prop) (i : I)
    (x : (∀ i, S i) × O) : Prop := CellPivotal (fun y => E (y,x.2)) i x.1

omit [∀ i, Fintype (A i)] in
theorem mixed_probability (K : ∀ i, A i → FiniteLaw (S i)) (μ : FiniteLaw O)
    (E : ((∀ i, S i) × O) → Prop) (e : ∀ i, A i) :
    probability (mixedKernel K μ e) E =
      μ.expect (fun o => probability (cellKernel K e) (fun x => E (x,o))) := by
  unfold probability mixedKernel
  rw [FiniteLaw.expect_prod, FiniteLaw.expect_comm]

omit [∀ i, Fintype (A i)] in
theorem conditional_resampling_abs (K : ∀ i, A i → FiniteLaw (S i))
    (E : (∀ i, S i) → Prop) (e : ∀ i, A i) (i : I) (a : A i) :
    |probability (cellKernel K e) E -
      probability (cellKernel K (Function.update e i a)) E| ≤
      probability (cellKernel K e) (CellPivotal E i) := by
  rw [conditionalProbability_split K E e i,
    conditionalProbability_split K E (Function.update e i a) i,
    outsideKernel_update, conditional_pivotal_eq]
  exact cell_sensitivity _ _ _ _

omit [∀ i, Fintype (A i)] in
/-- Independent exterior samples do not create additional environment
coordinates. They are averaged in the same sensitivity coupling. -/
theorem mixed_resampling_abs (K : ∀ i, A i → FiniteLaw (S i)) (μ : FiniteLaw O)
    (E : ((∀ i, S i) × O) → Prop) (e : ∀ i, A i) (i : I) (a : A i) :
    |probability (mixedKernel K μ e) E -
      probability (mixedKernel K μ (Function.update e i a)) E| ≤
      probability (mixedKernel K μ e) (activePivotal E i) := by
  simp only [mixed_probability]
  rw [← FiniteLaw.expect_sub]
  apply (μ.abs_expect_le _).trans
  exact μ.expect_mono (fun o => conditional_resampling_abs K (fun x => E (x,o)) e i a)

omit [∀ i, Fintype (A i)] in
theorem mixed_resampling_squared (K : ∀ i, A i → FiniteLaw (S i)) (μ : FiniteLaw O)
    (E : ((∀ i, S i) × O) → Prop) (e : ∀ i, A i) (i : I) (a : A i) :
    (probability (mixedKernel K μ e) E -
      probability (mixedKernel K μ (Function.update e i a)) E) ^ 2 ≤
      probability (mixedKernel K μ e) (activePivotal E i) ^ 2 := by
  have h := mul_self_le_mul_self (abs_nonneg _)
    (mixed_resampling_abs K μ E e i a)
  simpa only [← pow_two, sq_abs] using h

/-- The only variance input is the classical Efron--Stein inequality on
the active independent environments. The freshly averaged exterior has
no term in this sum. -/
theorem mixed_grouped_variance (ρ : ∀ i, FiniteLaw (A i))
    (K : ∀ i, A i → FiniteLaw (S i)) (μ : FiniteLaw O)
    (E : ((∀ i, S i) × O) → Prop) (hES : EfronStein ρ) :
    pairedProbability (FiniteLaw.pi ρ) (mixedKernel K μ) E -
      marginalProbability (FiniteLaw.pi ρ) (mixedKernel K μ) E ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i,
        pairedProbability (FiniteLaw.pi ρ) (mixedKernel K μ) (activePivotal E i) := by
  rw [paired_sub_marginal_sq]
  apply (hES (fun e => probability (mixedKernel K μ e) E)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  rw [pairedProbability_eq]
  apply FiniteLaw.expect_mono
  intro e
  calc
    _ ≤ (ρ i).expect (fun _ => probability (mixedKernel K μ e) (activePivotal E i) ^ 2) :=
      (ρ i).expect_mono (fun a => mixed_resampling_squared K μ E e i a)
    _ = _ := (ρ i).expect_const _

#print axioms mixed_resampling_abs
#print axioms mixed_grouped_variance

end

noncomputable section

open GroupedDimerLaw

variable {I O : Type*} [Fintype I] [Fintype O]
variable {J : I → Type*} [∀ i, Fintype (J i)]
variable {A S : (i : I) → J i → Type*}
variable [∀ i j, Fintype (A i j)] [∀ i j, Fintype (S i j)]

local instance : DecidableEq (Sigma J) := fun a b => Classical.propDecidable (a = b)

omit [∀ i j, Fintype (A i j)] in
theorem mixed_probability_nested (K : ∀ i j, A i j → FiniteLaw (S i j))
    (μ : FiniteLaw O) (E : (((s : Sigma J) → S s.1 s.2) × O) → Prop)
    (e : ∀ i j, A i j) :
    probability (mixedKernel (fun s : Sigma J => K s.1 s.2) μ (flatten e)) E =
      probability (mixedKernel (fun i a => cellKernel (K i) a) μ e)
        (fun x => E (flatten x.1,x.2)) := by
  unfold probability mixedKernel
  rw [FiniteLaw.expect_prod, FiniteLaw.expect_prod]
  exact expect_pi_nested (fun i j => K i j (e i j)) _

theorem mixed_paired_nested (ρ : ∀ i j, FiniteLaw (A i j))
    (K : ∀ i j, A i j → FiniteLaw (S i j))
    (μ : FiniteLaw O) (E : (((s : Sigma J) → S s.1 s.2) × O) → Prop) :
    pairedProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
      (mixedKernel (fun s : Sigma J => K s.1 s.2) μ) E =
    pairedProbability (FiniteLaw.pi (fun i => FiniteLaw.pi (ρ i)))
      (mixedKernel (fun i a => cellKernel (K i) a) μ) (fun x => E (flatten x.1,x.2)) := by
  simp only [pairedProbability_eq]
  rw [expect_pi_nested]
  exact FiniteLaw.expect_congr _ (fun e => congrArg (fun x : ℝ => x ^ 2)
    (mixed_probability_nested K μ E e))

theorem mixed_marginal_nested (ρ : ∀ i j, FiniteLaw (A i j))
    (K : ∀ i j, A i j → FiniteLaw (S i j))
    (μ : FiniteLaw O) (E : (((s : Sigma J) → S s.1 s.2) × O) → Prop) :
    marginalProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
      (mixedKernel (fun s : Sigma J => K s.1 s.2) μ) E =
    marginalProbability (FiniteLaw.pi (fun i => FiniteLaw.pi (ρ i)))
      (mixedKernel (fun i a => cellKernel (K i) a) μ) (fun x => E (flatten x.1,x.2)) := by
  unfold marginalProbability
  rw [expect_pi_nested]
  exact FiniteLaw.expect_congr _ (mixed_probability_nested K μ E)

def activeGroupPivotal (E : (((s : Sigma J) → S s.1 s.2) × O) → Prop)
    (i : I) (x : ((s : Sigma J) → S s.1 s.2) × O) : Prop :=
  GroupPivotal (fun y => E (y,x.2)) i x.1

/-- Regrouping active dimers into mesoscopic cells preserves the same
independent exterior and introduces no term for that exterior. -/
theorem mixed_nested_variance (ρ : ∀ i j, FiniteLaw (A i j))
    (K : ∀ i j, A i j → FiniteLaw (S i j))
    (μ : FiniteLaw O) (E : (((s : Sigma J) → S s.1 s.2) × O) → Prop)
    (hES : EfronStein (fun i => FiniteLaw.pi (ρ i))) :
    pairedProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
        (mixedKernel (fun s : Sigma J => K s.1 s.2) μ) E -
      marginalProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
        (mixedKernel (fun s : Sigma J => K s.1 s.2) μ) E ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i,
        pairedProbability (FiniteLaw.pi (fun s : Sigma J => ρ s.1 s.2))
          (mixedKernel (fun s : Sigma J => K s.1 s.2) μ) (activeGroupPivotal E i) := by
  simp only [mixed_paired_nested, mixed_marginal_nested, activeGroupPivotal]
  exact mixed_grouped_variance (fun i => FiniteLaw.pi (ρ i))
    (fun i a => cellKernel (K i) a) μ (fun x => E (flatten x.1,x.2)) hES

#print axioms mixed_nested_variance

end

end ExceptionalTimes.MixedEnvironmentVariance
