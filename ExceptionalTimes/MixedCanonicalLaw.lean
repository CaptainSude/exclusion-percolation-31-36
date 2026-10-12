import ExceptionalTimes.ManyDimerLaw

/-! Independent outside colors in two canonical replicas. This is full
independent resampling outside the active set, not the infinite-time
occupancy-preserving dimer law. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedCanonicalLaw

open FiniteHaar CanonicalHarris DimerLaw ManyDimerLaw

variable {A O : Type*} [Fintype A] [Fintype O]

noncomputable def smooth (F : ((A → Color) × (O → Color)) → ℝ)
    (a : A → Color) : ℝ := average (fun o : O → Color => F (a,o))

noncomputable def mixed (p : A → ℝ) (F : ((A → Color) × (O → Color)) → ℝ) : ℝ :=
  letI := coordinateAction (G := PairGroup) (I := Fin 2)
  canonical (G := PairGroup) p (smooth F)

noncomputable def mixedProbability (p : A → ℝ)
    (E : ((A → Color) × (O → Color)) → Prop) : ℝ :=
  mixed p (fun z => EnvironmentVariance.indicator (E z))

theorem real_canonical_eq_joint (p : A → ℝ) (f : (A → Color) → ℝ) :
    (let _ := coordinateAction (G := PairGroup) (I := Fin 2);
      canonical (G := PairGroup) p f) =
      ∑ a, ∑ b, manyWeight p a b * (f a * f b) := by
  let := coordinateAction (G := PairGroup) (I := Fin 2)
  symm
  have hs : (∑ a, ∑ b, manyWeight p a b * (f a * f b)) =
      average (fun a => f a * flagAverage p
        (fun s => average (fun g : A → PairGroup => f (refresh s g a)))) := by
    simp only [manyWeight_eq_canonicalKernel, average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    calc
      _ = (Fintype.card (A → Color) : ℝ)⁻¹ * (f a * ∑ b, canonicalKernel p a b * f b) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [canonicalKernel_expect]; simp only [average, Finset.mul_sum]
  rw [hs]
  simp_rw [← flagAverage_const_mul, ← average_const_mul]
  rw [average_flagAverage]
  unfold canonical conditional
  congr 1
  funext s
  rw [average_comm]
  apply congrArg (average (I := A → PairGroup))
  funext g
  unfold coefficient
  refine average_congr_instances _ _ _ _ (fun a => ?_)
  rfl

theorem mixed_eq_joint (p : A → ℝ) (F : ((A → Color) × (O → Color)) → ℝ) :
    mixed p F = ∑ a, ∑ b, manyWeight p a b * (smooth F a * smooth F b) :=
  real_canonical_eq_joint p (smooth F)

omit [Fintype A] in
theorem smooth_nonneg (F : ((A → Color) × (O → Color)) → ℝ)
    (hF : ∀ z, 0 ≤ F z) : ∀ a, 0 ≤ smooth F a :=
  fun a => average_nonneg (fun o => hF (a,o))

omit [Fintype A] in
theorem smooth_monotone (F : ((A → Color) × (O → Color)) → ℝ)
    (hF : Monotone F) : Monotone (smooth F) := by
  intro a b hab
  exact average_mono (fun o => hF ⟨hab,le_rfl⟩)

theorem mixed_mono (p : A → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (F H : ((A → Color) × (O → Color)) → ℝ)
    (hF : ∀ z, 0 ≤ F z) (hFH : ∀ z, F z ≤ H z) : mixed p F ≤ mixed p H := by
  rw [mixed_eq_joint,mixed_eq_joint]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hweight : 0 ≤ manyWeight p a b :=
    Finset.prod_nonneg (fun i _ => twoTimeWeight_nonneg (hp0 i) (hp1 i) _ _)
  apply mul_le_mul_of_nonneg_left _ hweight
  apply mul_le_mul
  · exact average_mono (fun o => hFH (a,o))
  · exact average_mono (fun o => hFH (b,o))
  · exact smooth_nonneg F hF b
  · exact average_nonneg (fun o => (hF (a,o)).trans (hFH (a,o)))

/-- Paired Harris survives full independent resampling outside the active
dimers. It is proved by first applying ordinary Harris to the outside
colors, and then canonical Harris to the increasing conditional means. -/
theorem mixed_association (p : A → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (F H : ((A → Color) × (O → Color)) → ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (hH0 : ∀ z, 0 ≤ H z)
    (hF : Monotone F) (hH : Monotone H) :
    mixed p F * mixed p H ≤ mixed p (fun z => F z * H z) := by
  let := coordinateAction (G := PairGroup) (I := Fin 2)
  have hact : ∀ g : PairGroup, Monotone (fun x : Color => g • x) := by
    intro g x y hxy i
    exact hxy (g⁻¹ • i)
  have hlocal (a : A → Color) : smooth F a * smooth H a ≤ smooth (fun z => F z * H z) a :=
    uniform_harris (fun o => F (a,o)) (fun o => H (a,o))
      (fun o => hF0 (a,o)) (fun o => hH0 (a,o))
      (fun _ _ h => hF ⟨le_rfl,h⟩) (fun _ _ h => hH ⟨le_rfl,h⟩)
  have hcanon := canonical_association hact p hp0 hp1 (smooth F) (smooth H)
    (smooth_nonneg F hF0) (smooth_nonneg H hH0) (smooth_monotone F hF) (smooth_monotone H hH)
  change canonical (G := PairGroup) p (smooth F) * canonical (G := PairGroup) p (smooth H) ≤ _
  refine hcanon.trans ?_
  rw [real_canonical_eq_joint,mixed_eq_joint]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hw : 0 ≤ manyWeight p a b :=
    Finset.prod_nonneg (fun i _ => twoTimeWeight_nonneg (hp0 i) (hp1 i) _ _)
  apply mul_le_mul_of_nonneg_left _ hw
  exact mul_le_mul (hlocal a) (hlocal b)
    (mul_nonneg (smooth_nonneg F hF0 b) (smooth_nonneg H hH0 b))
    (smooth_nonneg _ (fun z => mul_nonneg (hF0 z) (hH0 z)) a)

theorem mixed_square_lower (p : A → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (F : ((A → Color) × (O → Color)) → ℝ) :
    (average (smooth F))^2 ≤ mixed p F := by
  let := coordinateAction (G := PairGroup) (I := Fin 2)
  exact canonical_square_lower p hp0 hp1 (smooth F)

open EnvironmentVariance

theorem law_square_lower {S : Type*} [Fintype S] (μ : FiniteLaw S) (f : S → ℝ) :
    (μ.expect f)^2 ≤ μ.expect (fun s => (f s)^2) := by
  have h := μ.expect_nonneg (fun s => sq_nonneg (f s-μ.expect f))
  change 0 ≤ μ.variance f at h
  rw [FiniteLaw.variance_eq] at h
  linarith

theorem mixed_eq_environment_square (p : A → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (F : ((A → Color) × (O → Color)) → ℝ) :
    mixed p F = (manyEnvironment p hp0 hp1).expect
      (fun e => ((manyReplica e).expect (smooth F))^2) := by
  rw [mixed_eq_joint,many_expect_replica p hp0 hp1]
  simp only [FiniteLaw.expect_const_mul,FiniteLaw.expect_mul_const,pow_two]

/-- Both groups use their canonical law, independently of each other.
This finite conditional-replica expression retains the outside occupancy
information, unlike `mixed`. -/
noncomputable def bothCanonical (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (F : ((A → Color) × (O → Color)) → ℝ) : ℝ :=
  (manyEnvironment p hp0 hp1).expect (fun e =>
    (manyEnvironment q hq0 hq1).expect (fun d =>
      ((manyReplica e).expect (fun a => (manyReplica d).expect (fun o => F (a,o))))^2))

/-- Forgetting outside environments decreases every real quadratic
coefficient. In particular this comparison applies to nonmonotone arm
events as well as increasing radial events. -/
theorem mixed_le_bothCanonical (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (F : ((A → Color) × (O → Color)) → ℝ) :
    mixed p F ≤ bothCanonical p q hp0 hp1 hq0 hq1 F := by
  rw [mixed_eq_environment_square p hp0 hp1]
  apply FiniteLaw.expect_mono
  intro e
  have he : (manyEnvironment q hq0 hq1).expect (fun d =>
      (manyReplica e).expect (fun a => (manyReplica d).expect (fun o => F (a,o)))) =
      (manyReplica e).expect (smooth F) := by
    rw [FiniteLaw.expect_comm]
    apply FiniteLaw.expect_congr
    intro a
    exact many_marginal_expect q hq0 hq1 (fun o => F (a,o))
  rw [← he]
  exact law_square_lower _ _

#print axioms mixed_association
#print axioms mixed_le_bothCanonical

end ExceptionalTimes.MixedCanonicalLaw
