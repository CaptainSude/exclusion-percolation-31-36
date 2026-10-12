import ExceptionalTimes.DimerLaw

/-! One explicit finite product dimer law, with its conditional environment,
Harris association, and grouped pivotal variance bound. -/

open scoped BigOperators Classical
open ExceptionalTimes.FiniteHaar ExceptionalTimes.CanonicalHarris
open ExceptionalTimes.DimerLaw

namespace ExceptionalTimes.ManyDimerLaw

set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false



variable {B : Type*} [Fintype B]

theorem average_congr_instances {I : Type*} (FI FJ : Fintype I) (f h : I → ℝ)
    (he : ∀ i, f i = h i) : @average I FI f = @average I FJ h := by
  cases Subsingleton.elim FI FJ
  congr 1
  funext i
  exact he i

noncomputable def manyWeight (p : B → ℝ) (ω η : B → Color) : ℝ :=
  ∏ b, twoTimeWeight (p b) (ω b) (η b)

noncomputable def manyEnvironment (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) : EnvironmentVariance.FiniteLaw (B → Environment) :=
  EnvironmentVariance.FiniteLaw.pi (fun b => environmentLaw (p b) (hp0 b) (hp1 b))

noncomputable def manyReplica (e : B → Environment) : EnvironmentVariance.FiniteLaw (B → Color) :=
  EnvironmentVariance.cellKernel (fun _ : B => replicaLaw) e

theorem manyEnvironment_weight (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) (e : B → Environment) :
    (manyEnvironment p hp0 hp1).weight e = ∏ b, environmentWeight (p b) (e b) := rfl

theorem manyReplica_weight (e : B → Environment) (ω : B → Color) :
    (manyReplica e).weight ω = ∏ b, conditionalLaw (e b) (ω b) := rfl

/-- Exact tensorization of the single-dimer conditional iid law. -/
theorem manyWeight_replica (p : B → ℝ) (ω η : B → Color) :
    manyWeight p ω η =
      ∑ e : B → Environment, (∏ b, environmentWeight (p b) (e b)) *
        ((∏ b, conditionalLaw (e b) (ω b)) * ∏ b, conditionalLaw (e b) (η b)) := by
  unfold manyWeight
  simp_rw [environment_replica_law]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.prod_mul_distrib]

theorem many_marginal_weight (p : B → ℝ) (ω : B → Color) :
    (∑ e : B → Environment, (∏ b, environmentWeight (p b) (e b)) *
      ∏ b, conditionalLaw (e b) (ω b)) = (Fintype.card (B → Color) : ℝ)⁻¹ := by
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun b e => environmentWeight (p b) e * conditionalLaw e (ω b))]
  simp only [environment_marginal]
  simp

theorem many_marginal_expect (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) (f : (B → Color) → ℝ) :
    (manyEnvironment p hp0 hp1).expect (fun e => (manyReplica e).expect f) = average f := by
  simp only [EnvironmentVariance.FiniteLaw.expect, manyEnvironment, manyReplica, EnvironmentVariance.cellKernel,
    EnvironmentVariance.FiniteLaw.pi, environmentLaw, replicaLaw, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, many_marginal_weight]
  exact (Finset.mul_sum _ _ _).symm

/-- The literal event probability under the product of the explicit dimer joint laws. -/
noncomputable def manyProbability (p : B → ℝ) (E : (B → Color) → Prop) : ℝ :=
  ∑ ω, ∑ η, manyWeight p ω η * (EnvironmentVariance.indicator (E ω) * EnvironmentVariance.indicator (E η))

theorem mixture_expect {A S : Type*} [Fintype A] [Fintype S]
    (w : A → ℝ) (k : A → S → ℝ) (F : S → S → ℝ) :
    (∑ x, ∑ y, (∑ a, w a * (k a x * k a y)) * F x y) =
      ∑ a, w a * ∑ x, k a x * ∑ y, k a y * F x y := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ x : S, ∑ a : A, ∑ y : S, w a * (k a x * k a y) * F x y := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ a : A, ∑ x : S, ∑ y : S, w a * (k a x * k a y) * F x y :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

/-- The product joint law has the same expectation as conditionally iid product replicas. -/
theorem many_expect_replica (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) (F : (B → Color) → (B → Color) → ℝ) :
    (∑ ω, ∑ η, manyWeight p ω η * F ω η) =
      (manyEnvironment p hp0 hp1).expect (fun e => (manyReplica e).expect
        (fun ω => (manyReplica e).expect (F ω))) := by
  simp only [EnvironmentVariance.FiniteLaw.expect, manyEnvironment_weight, manyReplica_weight,
    manyWeight_replica]
  exact mixture_expect (A := B → Environment) (S := B → Color)
    (fun e : B → Environment => ∏ b, environmentWeight (p b) (e b))
    (fun (e : B → Environment) (ω : B → Color) => ∏ b, conditionalLaw (e b) (ω b)) F

theorem manyProbability_eq_paired (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) (E : (B → Color) → Prop) :
    manyProbability p E = EnvironmentVariance.pairedProbability (manyEnvironment p hp0 hp1) manyReplica E :=
  many_expect_replica p hp0 hp1 (fun ω η => EnvironmentVariance.indicator (E ω) * EnvironmentVariance.indicator (E η))

theorem manyWeight_total (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) :
    (∑ ω, ∑ η, manyWeight p ω η) = 1 := by
  simpa only [mul_one, EnvironmentVariance.FiniteLaw.expect_const] using
    many_expect_replica p hp0 hp1 (fun _ _ => 1)

/-- The normalized joint probability law of all finite dimers. -/
noncomputable def manyLaw (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) :
    EnvironmentVariance.FiniteLaw ((B → Color) × (B → Color)) where
  weight z := manyWeight p z.1 z.2
  nonneg z := Finset.prod_nonneg (fun b _ => twoTimeWeight_nonneg (hp0 b) (hp1 b) _ _)
  total := by rw [Fintype.sum_prod_type]; exact manyWeight_total p hp0 hp1

theorem manyProbability_eq_joint (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) (E : (B → Color) → Prop) :
    manyProbability p E =
      EnvironmentVariance.probability (manyLaw p hp0 hp1) (fun z => E z.1 ∧ E z.2) := by
  simp only [manyProbability, EnvironmentVariance.probability, EnvironmentVariance.FiniteLaw.expect,
    manyLaw, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro η _
  by_cases hω : E ω <;> by_cases hη : E η <;> simp [EnvironmentVariance.indicator, hω, hη]

theorem many_marginal_probability (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) (E : (B → Color) → Prop) :
    EnvironmentVariance.marginalProbability (manyEnvironment p hp0 hp1) manyReplica E =
      average (fun ω => EnvironmentVariance.indicator (E ω)) := many_marginal_expect p hp0 hp1 _

/-- The grouped pivotal variance bound for the actual finite product dimer law.
Its sole named inequality input is classical finite-product Efron--Stein. -/
theorem finite_dimer_variance (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b)
    (hp1 : ∀ b, p b ≤ 1) (E : (B → Color) → Prop)
    (hES : EnvironmentVariance.EfronStein (fun b => environmentLaw (p b) (hp0 b) (hp1 b))) :
    manyProbability p E - (average (fun ω => EnvironmentVariance.indicator (E ω)))^2 ≤
      (1 / 2 : ℝ) * ∑ b, manyProbability p (EnvironmentVariance.CellPivotal E b) := by
  simp_rw [manyProbability_eq_paired p hp0 hp1, ← many_marginal_probability p hp0 hp1]
  exact EnvironmentVariance.grouped_environment_variance _ _ E hES

theorem average_pi_product {R : Type*} [Fintype R] (f : B → R → ℝ) :
    average (fun r : B → R => ∏ b, f b (r b)) = ∏ b, average (f b) := by
  unfold average
  rw [← Fintype.prod_sum f, Finset.prod_mul_distrib]
  simp

theorem indicator_function_eq {R : Type*} [DecidableEq R] (x y : B → R) :
    (if x = y then (1 : ℝ) else 0) = ∏ b, if x b = y b then 1 else 0 := by
  by_cases h : x = y
  · subst y
    simp
  · rw [ite_eq_right h]
    obtain ⟨b, hb⟩ : ∃ b, x b ≠ y b := by
      by_contra hn
      apply h
      funext b
      exact not_not.mp (fun hb => hn ⟨b, hb⟩)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ b) (ite_eq_right hb)

local instance : MulAction PairGroup Color := coordinateAction

noncomputable def maskedKernel (s : B → Bool) (ω η : B → Color) : ℝ :=
  average (fun g : B → PairGroup => if refresh s g ω = η then 1 else 0)

theorem maskedKernel_product (s : B → Bool) (ω η : B → Color) :
    maskedKernel s ω η = ∏ b, if s b then haarTransition (ω b) (η b)
      else if ω b = η b then 1 else 0 := by
  unfold maskedKernel
  conv_lhs => enter [1, g]; rw [indicator_function_eq]
  change average (fun g : B → PairGroup => ∏ b,
    if mask s g b • ω b = η b then (1 : ℝ) else 0) = _
  unfold mask
  rw [average_pi_product (fun b g => if (if s b then g else 1) • ω b = η b then 1 else 0)]
  apply Finset.prod_congr rfl
  intro b _
  cases s b
  · simp [average_const]
  · simp only [↓reduceIte]
    rfl

noncomputable def canonicalKernel (p : B → ℝ) (ω η : B → Color) : ℝ :=
  flagAverage p (fun s => maskedKernel s ω η)

theorem canonicalKernel_product (p : B → ℝ) (ω η : B → Color) :
    canonicalKernel p ω η = ∏ b, ((1 - p b) * (if ω b = η b then 1 else 0) +
      p b * haarTransition (ω b) (η b)) := by
  unfold canonicalKernel flagAverage
  simp_rw [maskedKernel_product, flagWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun b (v : Bool) => (if v then p b else 1 - p b) *
    (if v then haarTransition (ω b) (η b) else if ω b = η b then 1 else 0))]
  apply Finset.prod_congr rfl
  intro b _
  simp [add_comm]

/-- The canonical flag/permutation sampler has exactly the product dimer joint mass. -/
theorem manyWeight_eq_canonicalKernel (p : B → ℝ) (ω η : B → Color) :
    manyWeight p ω η = (Fintype.card (B → Color) : ℝ)⁻¹ * canonicalKernel p ω η := by
  simp only [manyWeight, twoTimeWeight, Finset.prod_mul_distrib, canonicalKernel_product]
  congr 1
  simp

theorem flagAverage_mul_const (p : B → ℝ) (f : (B → Bool) → ℝ) (c : ℝ) :
    flagAverage p (fun s => f s * c) = flagAverage p f * c := by
  simp [flagAverage, Finset.sum_mul, mul_assoc]

theorem flagAverage_const_mul (p : B → ℝ) (c : ℝ) (f : (B → Bool) → ℝ) :
    flagAverage p (fun s => c * f s) = c * flagAverage p f := by
  simp [flagAverage, Finset.mul_sum, mul_left_comm]

theorem flagAverage_sum {I : Type*} [Fintype I] (p : B → ℝ) (f : (B → Bool) → I → ℝ) :
    flagAverage p (fun s => ∑ i, f s i) = ∑ i, flagAverage p (fun s => f s i) := by
  simp only [flagAverage, Finset.mul_sum]
  exact Finset.sum_comm

theorem average_flagAverage {I : Type*} [Fintype I] (p : B → ℝ)
    (f : I → (B → Bool) → ℝ) :
    average (fun i => flagAverage p (f i)) =
      flagAverage p (fun s => average (fun i => f i s)) := by
  simp only [flagAverage, average_sum, average_const_mul]

theorem canonicalKernel_expect (p : B → ℝ) (ω : B → Color) (f : (B → Color) → ℝ) :
    (∑ η, canonicalKernel p ω η * f η) =
      flagAverage p (fun s => average (fun g : B → PairGroup => f (refresh s g ω))) := by
  unfold canonicalKernel maskedKernel
  simp_rw [← flagAverage_mul_const, ← average_mul_const]
  rw [← flagAverage_sum]
  congr 1
  funext s
  rw [← average_sum]
  congr 1
  funext g
  simp

theorem manyProbability_eq_sampler (p : B → ℝ) (E : (B → Color) → Prop) :
    manyProbability p E = average (fun ω => EnvironmentVariance.indicator (E ω) *
      flagAverage p (fun s => average (fun g : B → PairGroup =>
        EnvironmentVariance.indicator (E (refresh s g ω))))) := by
  simp only [manyProbability, manyWeight_eq_canonicalKernel, average, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    _ = (Fintype.card (B → Color) : ℝ)⁻¹ * (EnvironmentVariance.indicator (E ω) *
        ∑ η, canonicalKernel p ω η * EnvironmentVariance.indicator (E η)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      ring
    _ = _ := by rw [canonicalKernel_expect]; simp only [average, Finset.mul_sum]

/-- The event probability appearing in finite-block Harris is exactly the same
product joint law used by the environment variance bound. -/
theorem manyProbability_eq_canonical (p : B → ℝ) (A : Set (B → Color)) :
    manyProbability p (fun ω => ω ∈ A) =
      blockCoordinateProbability (G := PairGroup) p A := by
  rw [manyProbability_eq_sampler]
  simp_rw [← flagAverage_const_mul, ← average_const_mul]
  rw [average_flagAverage]
  unfold blockCoordinateProbability canonicalProbability canonical conditional
  congr 1
  funext s
  rw [average_comm]
  apply congrArg (average (I := B → PairGroup))
  funext g
  unfold coefficient
  refine average_congr_instances _ _ _ _ (fun ω => ?_)
  rfl

/-- Duplicated Harris for the explicit product dimer law. -/
theorem many_harris (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (A D : Set (B → Color)) (hA : IsUpperSet A) (hD : IsUpperSet D) :
    manyProbability p (fun ω => ω ∈ A) * manyProbability p (fun ω => ω ∈ D) ≤
      manyProbability p (fun ω => ω ∈ A ∩ D) := by
  simp_rw [manyProbability_eq_canonical]
  exact block_coordinate_harris p hp0 hp1 A D hA hD

theorem many_square_lower (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : (B → Color) → Prop) :
    (average (fun ω => EnvironmentVariance.indicator (E ω)))^2 ≤ manyProbability p E := by
  rw [manyProbability_eq_paired p hp0 hp1, ← many_marginal_probability p hp0 hp1]
  apply sub_nonneg.mp
  rw [EnvironmentVariance.paired_sub_marginal_sq]
  exact EnvironmentVariance.FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)

/-- Finite canonical D and V for one and the same explicitly normalized law. -/
theorem finite_canonical_DV (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (A D : Set (B → Color)) (hA : IsUpperSet A) (hD : IsUpperSet D)
    (hES : EnvironmentVariance.EfronStein (fun b => environmentLaw (p b) (hp0 b) (hp1 b))) :
    (manyProbability p (fun ω => ω ∈ A) * manyProbability p (fun ω => ω ∈ D) ≤
      manyProbability p (fun ω => ω ∈ A ∩ D)) ∧
    ((average (eventIndicator A))^2 ≤ manyProbability p (fun ω => ω ∈ A)) ∧
    (manyProbability p (fun ω => ω ∈ A) - (average (eventIndicator A))^2 ≤
      (1 / 2 : ℝ) * ∑ b, manyProbability p (EnvironmentVariance.CellPivotal (fun ω => ω ∈ A) b)) :=
  ⟨many_harris p hp0 hp1 A D hA hD, many_square_lower p hp0 hp1 _,
    finite_dimer_variance p hp0 hp1 _ hES⟩

#print axioms manyProbability_eq_canonical
#print axioms finite_dimer_variance
#print axioms many_harris
#print axioms finite_canonical_DV

end ExceptionalTimes.ManyDimerLaw
