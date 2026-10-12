import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite conditional iid environments and the grouped pivotal variance bound.
All probability laws here are actual nonnegative normalized finite weights.
The only external input below is the explicitly stated classical Efron--Stein
inequality. In particular the pivotal sensitivity estimate is proved.
-/

open scoped BigOperators

namespace ExceptionalTimes.EnvironmentVariance

structure FiniteLaw (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def expect (μ : FiniteLaw A) (f : A → ℝ) : ℝ :=
  ∑ a, μ.weight a * f a

theorem expect_congr (μ : FiniteLaw A) {f g : A → ℝ} (h : ∀ a, f a = g a) :
    μ.expect f = μ.expect g := by simp only [expect, h]

@[simp] theorem expect_const (μ : FiniteLaw A) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  rw [expect, ← Finset.sum_mul, μ.total, one_mul]

theorem expect_add (μ : FiniteLaw A) (f g : A → ℝ) :
    μ.expect (fun a => f a + g a) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw A) (f g : A → ℝ) :
    μ.expect (fun a => f a - g a) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (μ : FiniteLaw A) (f : A → ℝ) (c : ℝ) :
    μ.expect (fun a => f a * c) = μ.expect f * c := by
  simp [expect, Finset.sum_mul, mul_assoc]

theorem expect_const_mul (μ : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    μ.expect (fun a => c * f a) = c * μ.expect f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

theorem expect_nonneg (μ : FiniteLaw A) {f : A → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ μ.expect f :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (μ.nonneg a) (h a))

theorem expect_mono (μ : FiniteLaw A) {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (μ.nonneg a))

theorem abs_expect_le (μ : FiniteLaw A) (f : A → ℝ) :
    |μ.expect f| ≤ μ.expect (fun a => |f a|) := by
  calc
    |μ.expect f| ≤ ∑ a, |μ.weight a * f a| := Finset.abs_sum_le_sum_abs _ _
    _ = μ.expect (fun a => |f a|) := by
      simp [expect, abs_mul, abs_of_nonneg (μ.nonneg _)]

theorem expect_comm (μ : FiniteLaw A) (ν : FiniteLaw B) (f : A → B → ℝ) :
    μ.expect (fun a => ν.expect (f a)) =
      ν.expect (fun b => μ.expect (fun a => f a b)) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

noncomputable def variance (μ : FiniteLaw A) (f : A → ℝ) : ℝ :=
  μ.expect (fun a => (f a - μ.expect f) ^ 2)

theorem variance_eq (μ : FiniteLaw A) (f : A → ℝ) :
    μ.variance f = μ.expect (fun a => f a ^ 2) - (μ.expect f) ^ 2 := by
  unfold variance
  simp only [sub_sq, expect_add, expect_sub, expect_const, expect_mul_const,
    expect_const_mul]
  ring

noncomputable def prod (μ : FiniteLaw A) (ν : FiniteLaw B) : FiniteLaw (A × B) where
  weight p := μ.weight p.1 * ν.weight p.2
  nonneg p := mul_nonneg (μ.nonneg p.1) (ν.nonneg p.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, μ.total]

theorem expect_prod (μ : FiniteLaw A) (ν : FiniteLaw B) (f : A × B → ℝ) :
    (μ.prod ν).expect f = μ.expect (fun a => ν.expect (fun b => f (a, b))) := by
  simp [expect, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

noncomputable def pi {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
    [∀ i, Fintype (S i)] (μ : ∀ i, FiniteLaw (S i)) : FiniteLaw (∀ i, S i) := by
  classical
  exact {
    weight := fun s => ∏ i, (μ i).weight (s i)
    nonneg := fun s => Finset.prod_nonneg (fun i _ => (μ i).nonneg (s i))
    total := by rw [← Fintype.prod_sum]; simp only [FiniteLaw.total, Finset.prod_const_one] }

theorem expect_pi_split {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*}
    [∀ i, Fintype (S i)] (μ : ∀ i, FiniteLaw (S i)) (i : I) (f : (∀ i, S i) → ℝ) :
    (pi μ).expect f = (μ i).expect (fun s =>
      (pi (fun j : {j // j ≠ i} => μ j)).expect
        (fun o => f ((Equiv.piSplitAt i S).symm (s, o)))) := by
  classical
  unfold expect
  rw [← (Equiv.piSplitAt i S).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  have hi : (Equiv.piSplitAt i S).symm (s, o) i = s := by simp [Equiv.piSplitAt]
  have ho : ∀ j : {j // j ≠ i}, (Equiv.piSplitAt i S).symm (s, o) j = o j := by
    intro j
    simp [Equiv.piSplitAt, j.property]
  dsimp [pi]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [hi, ho]
  ring

end FiniteLaw

noncomputable def indicator (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  classical
  simp only [indicator]
  split_ifs <;> norm_num

theorem indicator_le_one (P : Prop) : indicator P ≤ 1 := by
  classical
  simp only [indicator]
  split_ifs <;> norm_num

noncomputable def probability {A : Type*} [Fintype A] (μ : FiniteLaw A)
    (E : A → Prop) : ℝ := μ.expect (fun a => indicator (E a))

theorem probability_nonneg {A : Type*} [Fintype A] (μ : FiniteLaw A) (E : A → Prop) :
    0 ≤ probability μ E := μ.expect_nonneg (fun _ => indicator_nonneg _)

theorem probability_le_one {A : Type*} [Fintype A] (μ : FiniteLaw A) (E : A → Prop) :
    probability μ E ≤ 1 := by
  calc
    _ ≤ μ.expect (fun _ => 1) := μ.expect_mono (fun a => indicator_le_one _)
    _ = 1 := μ.expect_const _

section Replicas

variable {A S : Type*} [Fintype A] [Fintype S]

/-- Actual sampling: first an environment, then two conditionally iid replicas. -/
noncomputable def pairedProbability (ρ : FiniteLaw A) (K : A → FiniteLaw S)
    (E : S → Prop) : ℝ :=
  ρ.expect (fun a => (K a).expect (fun x =>
    (K a).expect (fun y => indicator (E x) * indicator (E y))))

theorem pairedProbability_eq (ρ : FiniteLaw A) (K : A → FiniteLaw S) (E : S → Prop) :
    pairedProbability ρ K E = ρ.expect (fun a => probability (K a) E ^ 2) := by
  unfold pairedProbability probability
  simp only [FiniteLaw.expect_const_mul, FiniteLaw.expect_mul_const, pow_two]

/-- The marginal is computed from the same explicit two-stage sampling law. -/
noncomputable def marginalProbability (ρ : FiniteLaw A) (K : A → FiniteLaw S)
    (E : S → Prop) : ℝ := ρ.expect (fun a => probability (K a) E)

theorem paired_sub_marginal_sq (ρ : FiniteLaw A) (K : A → FiniteLaw S)
    (E : S → Prop) :
    pairedProbability ρ K E - marginalProbability ρ K E ^ 2 =
      ρ.variance (fun a => probability (K a) E) := by
  rw [pairedProbability_eq, FiniteLaw.variance_eq]
  rfl

end Replicas

section Sensitivity

variable {O S : Type*} [Fintype O] [Fintype S]

/-- The outside configuration admits two inside assignments with opposite event values. -/
def Pivotal (E : O → S → Prop) (o : O) : Prop :=
  ∃ s t, ¬ (E o s ↔ E o t)

theorem inside_sensitivity (ν ν' : FiniteLaw S) (E : S → Prop) :
    |probability ν E - probability ν' E| ≤
      indicator (∃ s t, ¬ (E s ↔ E t)) := by
  classical
  by_cases hp : ∃ s t, ¬ (E s ↔ E t)
  · rw [indicator, ite_eq_left hp]
    apply abs_le.mpr
    constructor <;> linarith [probability_nonneg ν E, probability_le_one ν E,
      probability_nonneg ν' E, probability_le_one ν' E]
  · rw [indicator, ite_eq_right hp]
    by_cases hall : ∀ s, E s
    · have he : ∀ s, indicator (E s) = 1 := fun s => ite_eq_left (hall s)
      simp [probability, he]
    · obtain ⟨s, hs⟩ := not_forall.mp hall
      have hn : ∀ t, ¬ E t := by
        intro t ht
        exact hp ⟨s, t, fun h => hs (h.mpr ht)⟩
      have he : ∀ t, indicator (E t) = 0 := fun t => ite_eq_right (hn t)
      simp [probability, he]

/-- Coupling both outside configurations identically proves sensitivity; it is not an input. -/
theorem cell_sensitivity (μ : FiniteLaw O) (ν ν' : FiniteLaw S) (E : O → S → Prop) :
    |μ.expect (fun o => probability ν (E o)) -
      μ.expect (fun o => probability ν' (E o))| ≤ probability μ (Pivotal E) := by
  rw [← μ.expect_sub]
  exact (μ.abs_expect_le _).trans (μ.expect_mono (fun o => inside_sensitivity ν ν' (E o)))

theorem cell_sensitivity_squared (μ : FiniteLaw O) (ν ν' : FiniteLaw S)
    (E : O → S → Prop) :
    (μ.expect (fun o => probability ν (E o)) -
      μ.expect (fun o => probability ν' (E o))) ^ 2 ≤
      probability μ (Pivotal E) ^ 2 := by
  have h := cell_sensitivity μ ν ν' E
  have hs := mul_self_le_mul_self (abs_nonneg _) h
  simpa only [← pow_two, sq_abs] using hs

end Sensitivity

section IndependentCells

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A S : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (S i)]

/-- Each cell samples its own state from its own environment coordinate. -/
noncomputable def cellKernel (K : ∀ i, A i → FiniteLaw (S i)) (e : ∀ i, A i) :
    FiniteLaw (∀ i, S i) := FiniteLaw.pi (fun i => K i (e i))

noncomputable def outsideKernel (K : ∀ i, A i → FiniteLaw (S i))
    (e : ∀ i, A i) (i : I) : FiniteLaw (∀ j : {j // j ≠ i}, S j) :=
  FiniteLaw.pi (fun j => K j (e j))

def cellEvent (E : (∀ i, S i) → Prop) (i : I)
    (o : ∀ j : {j // j ≠ i}, S j) (s : S i) : Prop :=
  E ((Equiv.piSplitAt i S).symm (s, o))

/-- This event is defined on full configurations but ignores coordinate `i`. -/
def CellPivotal (E : (∀ i, S i) → Prop) (i : I) (x : ∀ i, S i) : Prop :=
  Pivotal (cellEvent E i) ((Equiv.piSplitAt i S) x).2

omit [∀ i, Fintype (A i)] in
theorem conditionalProbability_split (K : ∀ i, A i → FiniteLaw (S i))
    (E : (∀ i, S i) → Prop) (e : ∀ i, A i) (i : I) :
    probability (cellKernel K e) E =
      (outsideKernel K e i).expect (fun o => probability (K i (e i)) (cellEvent E i o)) := by
  unfold probability cellKernel
  rw [FiniteLaw.expect_pi_split _ i, FiniteLaw.expect_comm]
  rfl

omit [∀ i, Fintype (A i)] in
theorem outsideKernel_update (K : ∀ i, A i → FiniteLaw (S i))
    (e : ∀ i, A i) (i : I) (a : A i) :
    outsideKernel K (Function.update e i a) i = outsideKernel K e i := by
  unfold outsideKernel
  congr 1
  funext j
  rw [Function.update_of_ne j.property]

omit [∀ i, Fintype (A i)] in
theorem conditional_pivotal_eq (K : ∀ i, A i → FiniteLaw (S i))
    (E : (∀ i, S i) → Prop) (e : ∀ i, A i) (i : I) :
    probability (cellKernel K e) (CellPivotal E i) =
      probability (outsideKernel K e i) (Pivotal (cellEvent E i)) := by
  rw [conditionalProbability_split K (CellPivotal E i) e i]
  unfold probability
  apply FiniteLaw.expect_congr
  intro o
  simp only [cellEvent, CellPivotal, Equiv.apply_symm_apply]
  exact FiniteLaw.expect_const _ _

omit [∀ i, Fintype (A i)] in
/-- Resampling one genuine independent cell cannot change the event probability
by more than its outside pivotal probability. No sensitivity premise occurs. -/
theorem conditional_resampling_squared (K : ∀ i, A i → FiniteLaw (S i))
    (E : (∀ i, S i) → Prop) (e : ∀ i, A i) (i : I) (a : A i) :
    (probability (cellKernel K e) E -
      probability (cellKernel K (Function.update e i a)) E) ^ 2 ≤
      probability (cellKernel K e) (CellPivotal E i) ^ 2 := by
  rw [conditionalProbability_split K E e i,
    conditionalProbability_split K E (Function.update e i a) i,
    outsideKernel_update, conditional_pivotal_eq]
  exact cell_sensitivity_squared _ _ _ _

/-- Exact finite-product Efron--Stein theorem, isolated as the classical external
input. This is the general resampling variance inequality, not a percolation
correlation or pivotal estimate. -/
def EfronStein (ρ : ∀ i, FiniteLaw (A i)) : Prop :=
  ∀ f : (∀ i, A i) → ℝ,
    (FiniteLaw.pi ρ).variance f ≤
      (1 / 2 : ℝ) * ∑ i, (FiniteLaw.pi ρ).expect (fun e =>
        (ρ i).expect (fun a => (f e - f (Function.update e i a)) ^ 2))

/-- The manuscript's grouped environment variance inequality. The proof derives
all pivotal and iid-replica steps from explicit finite laws and kernels; its one
remaining named input is the classical finite-product Efron--Stein inequality. -/
theorem grouped_environment_variance (ρ : ∀ i, FiniteLaw (A i))
    (K : ∀ i, A i → FiniteLaw (S i)) (E : (∀ i, S i) → Prop)
    (hES : EfronStein ρ) :
    pairedProbability (FiniteLaw.pi ρ) (cellKernel K) E -
      marginalProbability (FiniteLaw.pi ρ) (cellKernel K) E ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i,
        pairedProbability (FiniteLaw.pi ρ) (cellKernel K) (CellPivotal E i) := by
  rw [paired_sub_marginal_sq]
  apply (hES (fun e => probability (cellKernel K e) E)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  rw [pairedProbability_eq]
  apply FiniteLaw.expect_mono
  intro e
  calc
    _ ≤ (ρ i).expect (fun _ => probability (cellKernel K e) (CellPivotal E i) ^ 2) :=
      (ρ i).expect_mono (fun a => conditional_resampling_squared K E e i a)
    _ = _ := (ρ i).expect_const _

end IndependentCells

end ExceptionalTimes.EnvironmentVariance

#print axioms ExceptionalTimes.EnvironmentVariance.paired_sub_marginal_sq
#print axioms ExceptionalTimes.EnvironmentVariance.cell_sensitivity_squared
#print axioms ExceptionalTimes.EnvironmentVariance.grouped_environment_variance
