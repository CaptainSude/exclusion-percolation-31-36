import ExceptionalTimes.CanonicalHarris
import ExceptionalTimes.EnvironmentVariance
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

/-! Explicit finite dimer refresh law and conditional independent replicas. -/

open scoped BigOperators Classical
open ExceptionalTimes.FiniteHaar ExceptionalTimes.CanonicalHarris

namespace ExceptionalTimes.DimerLaw

abbrev Color := Fin 2 → Bool
abbrev PairGroup := Equiv.Perm (Fin 2)

def pair (a b : Bool) : Color := fun i => if i = 0 then a else b

def swap : PairGroup := Equiv.swap 0 1

theorem pair_ext (ω : Color) : pair (ω 0) (ω 1) = ω := by
  funext i
  fin_cases i <;> simp [pair]

def colorEquiv : Color ≃ Bool × Bool where
  toFun ω := (ω 0, ω 1)
  invFun ab := pair ab.1 ab.2
  left_inv := pair_ext
  right_inv ab := by simp [pair]

theorem sum_color (f : Color → ℝ) :
    ∑ ω, f ω = f (pair false false) + f (pair false true) +
      f (pair true false) + f (pair true true) := by
  rw [← Equiv.sum_comp colorEquiv.symm]
  simp [Fintype.sum_prod_type, colorEquiv, add_comm, add_assoc]

theorem color_card : Fintype.card Color = 4 := by decide

theorem average_color (f : Color → ℝ) :
    average f = (f (pair false false) + f (pair false true) +
      f (pair true false) + f (pair true true)) / 4 := by
  rw [average, color_card, sum_color]
  ring

theorem pairGroup_univ : (Finset.univ : Finset PairGroup) = {1, swap} := by decide

/-- Haar averaging on a pair is exactly the average of identity and swap. -/
theorem average_pairGroup (f : PairGroup → ℝ) : average f = (f 1 + f swap) / 2 := by
  unfold average
  rw [Fintype.card_perm, pairGroup_univ]
  have hs : (1 : PairGroup) ≠ swap := by decide
  simp [hs]
  ring

noncomputable def refreshProbability (t : ℝ) : ℝ := 1 - Real.exp (-t)

theorem refreshProbability_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ refreshProbability t := by
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))

theorem refreshProbability_le_one (t : ℝ) : refreshProbability t ≤ 1 := by
  unfold refreshProbability
  linarith [Real.exp_pos (-t)]

/-- The finite canonical dimer duplicated Harris inequality at every nonnegative time. -/
theorem finite_dimer_harris {B : Type*} [Fintype B] (t : ℝ) (ht : 0 ≤ t)
    (A D : Set (B → Color)) (hA : IsUpperSet A) (hD : IsUpperSet D) :
    blockCoordinateProbability (G := PairGroup) (fun _ => refreshProbability t) A *
        blockCoordinateProbability (G := PairGroup) (fun _ => refreshProbability t) D ≤
      blockCoordinateProbability (G := PairGroup) (fun _ => refreshProbability t) (A ∩ D) :=
  finite_block_harris _ (refreshProbability_nonneg ht) (refreshProbability_le_one t) A D hA hD

theorem color_cases (ω : Color) : ∃ a b, ω = pair a b :=
  ⟨ω 0, ω 1, (pair_ext ω).symm⟩

@[simp] theorem pair_eq_pair (a b c d : Bool) : pair a b = pair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa [pair] using congrFun h 0, by simpa [pair] using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def act (g : PairGroup) (ω : Color) : Color := fun i => ω (g⁻¹ i)

def swapped (ω : Color) : Color := pair (ω 1) (ω 0)

@[simp] theorem act_one (ω : Color) : act 1 ω = ω := rfl

@[simp] theorem act_swap (ω : Color) : act swap ω = swapped ω := by
  funext i
  fin_cases i <;> simp [act, swap, swapped, pair]

/-- Number of black sites in the pair. -/
def blackCount (ω : Color) : Fin 3 :=
  if ω 0 then (if ω 1 then 2 else 1) else (if ω 1 then 1 else 0)

/-- Uniform conditional law on configurations with a prescribed black count. -/
noncomputable def countLaw (k : Fin 3) (ω : Color) : ℝ :=
  if blackCount ω = k then (if k = 1 then 1 / 2 else 1) else 0

theorem countLaw_nonneg (k : Fin 3) (ω : Color) : 0 ≤ countLaw k ω := by
  unfold countLaw
  split_ifs <;> norm_num

theorem countLaw_total (k : Fin 3) : ∑ ω, countLaw k ω = 1 := by
  rw [sum_color]
  fin_cases k <;> norm_num [countLaw, blackCount, pair]

/-- The finite Haar transition kernel on a dimer. -/
noncomputable def haarTransition (ω η : Color) : ℝ :=
  average (fun g : PairGroup => if act g ω = η then 1 else 0)

theorem haarTransition_identity_swap (ω η : Color) :
    haarTransition ω η = ((if ω = η then 1 else 0) +
      (if swapped ω = η then 1 else 0)) / 2 := by
  rw [haarTransition, average_pairGroup]
  rw [act_one, act_swap]

theorem haar_average_function (f : Color → ℝ) (ω : Color) :
    average (fun g : PairGroup => f (act g ω)) = (f ω + f (swapped ω)) / 2 := by
  rw [average_pairGroup, act_one, act_swap]

/-- Haar permutation refresh is exactly uniform resampling at fixed black count. -/
theorem haarTransition_eq_countLaw (ω η : Color) :
    haarTransition ω η = countLaw (blackCount ω) η := by
  obtain ⟨a, b, rfl⟩ := color_cases ω
  obtain ⟨c, d, rfl⟩ := color_cases η
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [haarTransition_identity_swap, swapped, pair, countLaw, blackCount, pair_eq_pair]

/-- Environment: full pair when unrefreshed, black count when refreshed. -/
abbrev Environment := Color ⊕ Fin 3

noncomputable def countMass (k : Fin 3) : ℝ := if k = 1 then 1 / 2 else 1 / 4

noncomputable def environmentWeight (p : ℝ) : Environment → ℝ
  | Sum.inl _ => (1 - p) / 4
  | Sum.inr k => p * countMass k

noncomputable def conditionalLaw : Environment → Color → ℝ
  | Sum.inl η, ω => if ω = η then 1 else 0
  | Sum.inr k, ω => countLaw k ω

/-- Information retained by a refresh flag and its initial pair. -/
def recordEnvironment (refreshed : Bool) (ω : Color) : Environment :=
  if refreshed then Sum.inr (blackCount ω) else Sum.inl ω

theorem blackCount_distribution (k : Fin 3) :
    average (fun ω : Color => if blackCount ω = k then (1 : ℝ) else 0) = countMass k := by
  rw [average_color]
  fin_cases k <;> norm_num [blackCount, pair, countMass]

/-- The environment weight is exactly the law obtained by sampling the flag
and a uniform pair, then recording the specified information. -/
theorem environmentWeight_eq_recordedLaw (p : ℝ) (e : Environment) :
    environmentWeight p e =
      (1 - p) * average (fun ω : Color => if recordEnvironment false ω = e then 1 else 0) +
        p * average (fun ω : Color => if recordEnvironment true ω = e then 1 else 0) := by
  cases e with
  | inl η =>
    obtain ⟨a, b, rfl⟩ := color_cases η
    cases a <;> cases b <;>
      norm_num [environmentWeight, average_color, recordEnvironment, pair, pair_eq_pair]
    all_goals ring
  | inr k =>
    fin_cases k <;>
      norm_num [environmentWeight, average_color, recordEnvironment, pair, blackCount, countMass]

theorem environmentWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (e : Environment) : 0 ≤ environmentWeight p e := by
  cases e with
  | inl ω => exact div_nonneg (sub_nonneg.mpr hp1) (by norm_num)
  | inr k =>
    apply mul_nonneg hp0
    unfold countMass
    split_ifs <;> norm_num

theorem environmentWeight_total (p : ℝ) : ∑ e, environmentWeight p e = 1 := by
  simp only [Fintype.sum_sum_type]
  rw [sum_color]
  norm_num [environmentWeight, countMass, Fin.sum_univ_succ]
  ring

theorem conditionalLaw_nonneg (e : Environment) (ω : Color) : 0 ≤ conditionalLaw e ω := by
  cases e with
  | inl η => change 0 ≤ (if ω = η then (1 : ℝ) else 0); split_ifs <;> norm_num
  | inr k => exact countLaw_nonneg k ω

theorem conditionalLaw_total (e : Environment) : ∑ ω, conditionalLaw e ω = 1 := by
  cases e with
  | inl η => simp [conditionalLaw]
  | inr k => exact countLaw_total k

/-- Explicit stationary two-time law: uniform initial pair, then either no refresh
or the identity/swap average. -/
noncomputable def twoTimeWeight (p : ℝ) (ω η : Color) : ℝ :=
  (1 / 4) * ((1 - p) * (if ω = η then 1 else 0) + p * haarTransition ω η)

/-- The two times are independent identically distributed samples conditional on
the recorded environment. This is an exact equality of the finite joint masses. -/
theorem environment_replica_law (p : ℝ) (ω η : Color) :
    twoTimeWeight p ω η =
      ∑ e, environmentWeight p e * (conditionalLaw e ω * conditionalLaw e η) := by
  obtain ⟨a, b, rfl⟩ := color_cases ω
  obtain ⟨c, d, rfl⟩ := color_cases η
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [twoTimeWeight, haarTransition_eq_countLaw, Fintype.sum_sum_type,
      sum_color, environmentWeight, conditionalLaw, countMass, countLaw,
      blackCount, pair, pair_eq_pair, Fin.sum_univ_succ] <;> ring

/-- The initial and final marginal laws are uniform on the four pair colors. -/
theorem environment_marginal (p : ℝ) (ω : Color) :
    (∑ e, environmentWeight p e * conditionalLaw e ω) = 1 / 4 := by
  obtain ⟨a, b, rfl⟩ := color_cases ω
  cases a <;> cases b <;>
    norm_num [Fintype.sum_sum_type, sum_color, environmentWeight, conditionalLaw,
      countMass, countLaw, blackCount, pair, pair_eq_pair, Fin.sum_univ_succ] <;> ring

theorem twoTimeWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω η : Color) :
    0 ≤ twoTimeWeight p ω η := by
  rw [environment_replica_law]
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (environmentWeight_nonneg hp0 hp1 e)
    (mul_nonneg (conditionalLaw_nonneg e ω) (conditionalLaw_nonneg e η)))

theorem twoTimeWeight_rowSum (p : ℝ) (ω : Color) : ∑ η, twoTimeWeight p ω η = 1 / 4 := by
  calc
    _ = (1 / 4) * ((1 - p) * (∑ η : Color, if ω = η then (1 : ℝ) else 0) +
        p * ∑ η, countLaw (blackCount ω) η) := by
      simp only [twoTimeWeight, haarTransition_eq_countLaw, Finset.mul_sum,
        mul_add, Finset.sum_add_distrib]
    _ = _ := by simp [countLaw_total]

theorem twoTimeWeight_total (p : ℝ) : ∑ ω, ∑ η, twoTimeWeight p ω η = 1 := by
  simp [twoTimeWeight_rowSum]

/-- All sixteen entries of the stationary four-state dimer law, in one formula.
The mixed-color diagonal entries are `(2-p)/8`, mixed-color off-diagonal entries
are `p/8`, and each monochromatic diagonal entry is `1/4`. -/
theorem twoTimeWeight_formula (p : ℝ) (ω η : Color) :
    twoTimeWeight p ω η =
      if ω = η then (if blackCount ω = 1 then (2 - p) / 8 else 1 / 4)
      else if blackCount ω = blackCount η then p / 8 else 0 := by
  obtain ⟨a, b, rfl⟩ := color_cases ω
  obtain ⟨c, d, rfl⟩ := color_cases η
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [twoTimeWeight, haarTransition_eq_countLaw, countLaw, blackCount, pair, pair_eq_pair] <;> ring

/-- Actual normalized finite law of the recorded dimer environment. -/
noncomputable def environmentLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    EnvironmentVariance.FiniteLaw Environment where
  weight := environmentWeight p
  nonneg := environmentWeight_nonneg hp0 hp1
  total := environmentWeight_total p

/-- Actual normalized conditional sampling law for either replica. -/
noncomputable def replicaLaw (e : Environment) : EnvironmentVariance.FiniteLaw Color where
  weight := conditionalLaw e
  nonneg := conditionalLaw_nonneg e
  total := conditionalLaw_total e

/-- The normalized four-state two-time law. -/
noncomputable def jointLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    EnvironmentVariance.FiniteLaw (Color × Color) where
  weight z := twoTimeWeight p z.1 z.2
  nonneg z := twoTimeWeight_nonneg hp0 hp1 z.1 z.2
  total := by rw [Fintype.sum_prod_type]; exact twoTimeWeight_total p

/-- The conditional replica marginal is the uniform initial Bernoulli pair law. -/
theorem replica_marginal_expect (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Color → ℝ) :
    (environmentLaw p hp0 hp1).expect (fun e => (replicaLaw e).expect f) = average f := by
  simp only [EnvironmentVariance.FiniteLaw.expect, environmentLaw, replicaLaw,
    Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, environment_marginal]
  norm_num [average, color_card, Finset.mul_sum]

/-- Equality of the entire two-time law and the conditional iid construction,
tested against an arbitrary function of the two configurations. -/
theorem jointLaw_expect (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Color → Color → ℝ) :
    (jointLaw p hp0 hp1).expect (fun z => F z.1 z.2) =
      (environmentLaw p hp0 hp1).expect (fun e => (replicaLaw e).expect
        (fun ω => (replicaLaw e).expect (F ω))) := by
  simp only [EnvironmentVariance.FiniteLaw.expect, jointLaw, environmentLaw, replicaLaw,
    Fintype.sum_prod_type, environment_replica_law, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ ω, ∑ e, ∑ η, environmentWeight p e *
        (conditionalLaw e ω * conditionalLaw e η) * F ω η := by
      apply Finset.sum_congr rfl
      intro ω _
      exact Finset.sum_comm
    _ = ∑ e, ∑ ω, ∑ η, environmentWeight p e *
        (conditionalLaw e ω * conditionalLaw e η) * F ω η := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.sum_congr rfl
      intro η _
      ring

/-- The exact duplicated-event probability is the paired probability consumed
by the generic environment-variance theorem. -/
theorem joint_probability_eq_paired (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Color → Prop) :
    EnvironmentVariance.probability (jointLaw p hp0 hp1) (fun z => E z.1 ∧ E z.2) =
      EnvironmentVariance.pairedProbability (environmentLaw p hp0 hp1) replicaLaw E := by
  have hi (ω η : Color) : EnvironmentVariance.indicator (E ω ∧ E η) =
      EnvironmentVariance.indicator (E ω) * EnvironmentVariance.indicator (E η) := by
    by_cases hω : E ω <;> by_cases hη : E η <;>
      simp [EnvironmentVariance.indicator, hω, hη]
  unfold EnvironmentVariance.probability EnvironmentVariance.pairedProbability
  simp_rw [hi]
  exact jointLaw_expect p hp0 hp1
    (fun ω η => EnvironmentVariance.indicator (E ω) * EnvironmentVariance.indicator (E η))

/-- Concrete dimer duplicated-event excess equals variance over its actual environment. -/
theorem dimer_probability_variance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Color → Prop) :
    EnvironmentVariance.probability (jointLaw p hp0 hp1) (fun z => E z.1 ∧ E z.2) -
        (average (fun ω => EnvironmentVariance.indicator (E ω)))^2 =
      (environmentLaw p hp0 hp1).variance
        (fun e => EnvironmentVariance.probability (replicaLaw e) E) := by
  rw [joint_probability_eq_paired]
  have hm : EnvironmentVariance.marginalProbability (environmentLaw p hp0 hp1) replicaLaw E =
      average (fun ω => EnvironmentVariance.indicator (E ω)) :=
    replica_marginal_expect p hp0 hp1 _
  rw [← hm]
  exact EnvironmentVariance.paired_sub_marginal_sq _ _ _

#print axioms finite_dimer_harris
#print axioms haarTransition_eq_countLaw
#print axioms environmentWeight_eq_recordedLaw
#print axioms twoTimeWeight_formula
#print axioms environment_replica_law
#print axioms dimer_probability_variance

end ExceptionalTimes.DimerLaw
