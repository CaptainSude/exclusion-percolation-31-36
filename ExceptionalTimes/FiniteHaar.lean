import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Finite Haar averaging, proved by finite sums. -/

open scoped BigOperators

namespace ExceptionalTimes.FiniteHaar

noncomputable def average {I : Type*} [Fintype I] (f : I → ℝ) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ∑ i, f i

theorem average_const {I : Type*} [Fintype I] [Nonempty I] (c : ℝ) :
    average (fun _ : I => c) = c := by
  simp [average, Fintype.card_ne_zero]

theorem average_add {I : Type*} [Fintype I] (f h : I → ℝ) :
    average (fun i => f i + h i) = average f + average h := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub {I : Type*} [Fintype I] (f h : I → ℝ) :
    average (fun i => f i - h i) = average f - average h := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_mul_const {I : Type*} [Fintype I] (f : I → ℝ) (c : ℝ) :
    average (fun i => f i * c) = average f * c := by
  simp [average, Finset.sum_mul, mul_assoc]

theorem average_const_mul {I : Type*} [Fintype I] (c : ℝ) (f : I → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp [average, Finset.mul_sum, mul_left_comm]

theorem average_sum {I J : Type*} [Fintype I] [Fintype J] (f : I → J → ℝ) :
    average (fun i => ∑ j, f i j) = ∑ j, average (fun i => f i j) := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_comm

theorem average_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : J → ℝ) : average (fun i => f (e i)) = average f := by
  simp only [average, Fintype.card_congr e, e.sum_comp]

theorem average_comm {I J : Type*} [Fintype I] [Fintype J] (f : I → J → ℝ) :
    average (fun i => average (fun j => f i j)) =
      average (fun j => average (fun i => f i j)) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def dot {S : Type*} [Fintype S] (f h : S → ℝ) : ℝ :=
  ∑ x, f x * h x

noncomputable def reynolds {G S : Type*} [Group G] [Fintype G] [MulAction G S]
    (f : S → ℝ) (x : S) : ℝ := average (fun g : G => f (g • x))

variable {G S : Type*} [Group G] [Fintype G] [Fintype S] [MulAction G S]

omit [Fintype S] in
theorem reynolds_invariant (f : S → ℝ) (g : G) (x : S) :
    reynolds (G := G) f (g • x) = reynolds (G := G) f x := by
  unfold reynolds
  simp only [← mul_smul]
  exact average_equiv (Equiv.mulRight g) (fun k : G => f (k • x))

theorem dot_comm (f h : S → ℝ) : dot f h = dot h f := by
  simp [dot, mul_comm]

theorem dot_reynolds (f h : S → ℝ) :
    dot f (reynolds (G := G) h) =
      average (fun g : G => dot f (fun x => h (g • x))) := by
  simp only [dot, reynolds, average_sum, average_const_mul]

theorem dot_invariant (f h : S → ℝ)
    (hh : ∀ (g : G) x, h (g • x) = h x) :
    dot (reynolds (G := G) f) h = dot f h := by
  calc
    dot (reynolds (G := G) f) h =
        average (fun g : G => ∑ x, f (g • x) * h x) := by
      simp only [dot, reynolds, average_sum, average_mul_const]
    _ = average (fun _ : G => dot f h) := by
      congr 1
      funext g
      rw [show (∑ x, f (g • x) * h x) = ∑ x, f (g • x) * h (g • x) by
        simp only [hh]]
      exact Equiv.sum_comp (MulAction.toPerm g) (fun x => f x * h x)
    _ = dot f h := average_const _

theorem dot_reynolds_square (f : S → ℝ) :
    dot f (reynolds (G := G) f) =
      dot (reynolds (G := G) f) (reynolds (G := G) f) := by
  exact (dot_invariant f _ (reynolds_invariant f)).symm

theorem dot_square_lower (p k : S → ℝ) (hk : dot p k = dot k k) :
    dot k k ≤ dot p p := by
  have hs : 0 ≤ ∑ x, (p x - k x) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (∑ x, (p x - k x) ^ 2) = dot p p - 2 * dot p k + dot k k := by
    simp only [sub_sq]
    simp [dot, pow_two, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [he, hk] at hs
  linarith

/-- The averaged coefficient dominates the squared norm of any invariant component. -/
theorem projection_lower (f k : S → ℝ)
    (hk : ∀ (g : G) x, k (g • x) = k x) (hf : dot f k = dot k k) :
    dot k k ≤ dot f (reynolds (G := G) f) := by
  rw [dot_reynolds_square]
  exact dot_square_lower _ _ ((dot_invariant f k hk).trans hf)

theorem dot_tensor {T : Type*} [Fintype T] (f v : S → ℝ) (h w : T → ℝ) :
    dot (fun z : S × T => f z.1 * h z.2) (fun z => v z.1 * w z.2) =
      dot f v * dot h w := by
  simp only [dot, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Nonnegative Haar covariance of real autocorrelation coefficients.
The finite state sums here are unnormalized; `haar_covariance` below gives
the uniform probability version. -/
theorem haar_covariance_sum {T : Type*} [Fintype T] [MulAction G T]
    (f : S → ℝ) (h : T → ℝ) :
    average (fun g : G => dot f (fun x => f (g • x))) *
        average (fun g : G => dot h (fun y => h (g • y))) ≤
      average (fun g : G =>
        dot f (fun x => f (g • x)) * dot h (fun y => h (g • y))) := by
  let F : S × T → ℝ := fun z => f z.1 * h z.2
  let K : S × T → ℝ := fun z =>
    reynolds (G := G) f z.1 * reynolds (G := G) h z.2
  have hK : ∀ (g : G) z, K (g • z) = K z := by
    intro g z
    change reynolds (G := G) f (g • z.1) * reynolds (G := G) h (g • z.2) = _
    rw [reynolds_invariant, reynolds_invariant]
  have hFK : dot F K = dot K K := by
    dsimp [F, K]
    rw [dot_tensor, dot_tensor, dot_reynolds_square, dot_reynolds_square]
  calc
    _ = dot K K := by
      dsimp [K]
      rw [dot_tensor, ← dot_reynolds_square, ← dot_reynolds_square,
        dot_reynolds, dot_reynolds]
    _ ≤ dot F (reynolds (G := G) F) := projection_lower F K hK hFK
    _ = _ := by
      rw [dot_reynolds]
      congr 1
      funext g
      change dot (fun z : S × T => f z.1 * h z.2)
        (fun z => f (g • z.1) * h (g • z.2)) = _
      exact dot_tensor f (fun x => f (g • x)) h (fun y => h (g • y))

/-- The autocorrelation with respect to the uniform law on the finite state space. -/
noncomputable def coefficient (f : S → ℝ) (g : G) : ℝ :=
  average (fun x => f x * f (g • x))

omit [Fintype G] in
theorem coefficient_eq (f : S → ℝ) (g : G) :
    coefficient f g = (Fintype.card S : ℝ)⁻¹ * dot f (fun x => f (g • x)) := rfl

/-- The Haar permutation covariance inequality for uniform finite state spaces.
It holds for arbitrary real functions, with no monotonicity hypothesis. -/
theorem haar_covariance {T : Type*} [Fintype T] [MulAction G T]
    (f : S → ℝ) (h : T → ℝ) :
    average (fun g : G => coefficient f g) * average (fun g : G => coefficient h g) ≤
      average (fun g : G => coefficient f g * coefficient h g) := by
  simp only [coefficient_eq, average_const_mul]
  have he (g : G) :
      ((Fintype.card S : ℝ)⁻¹ * dot f (fun x => f (g • x))) *
        ((Fintype.card T : ℝ)⁻¹ * dot h (fun x => h (g • x))) =
      ((Fintype.card S : ℝ)⁻¹ * (Fintype.card T : ℝ)⁻¹) *
        (dot f (fun x => f (g • x)) * dot h (fun x => h (g • x))) := by ring
  simp_rw [he, average_const_mul]
  calc
    _ = ((Fintype.card S : ℝ)⁻¹ * (Fintype.card T : ℝ)⁻¹) *
        (average (fun g : G => dot f (fun x => f (g • x))) *
          average (fun g : G => dot h (fun x => h (g • x)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (haar_covariance_sum f h) (by positivity)

theorem average_mono {I : Type*} [Fintype I] {f h : I → ℝ}
    (hle : ∀ i, f i ≤ h i) : average f ≤ average h := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hle i)) (by positivity)

theorem average_nonneg {I : Type*} [Fintype I] {f : I → ℝ}
    (hf : ∀ i, 0 ≤ f i) : 0 ≤ average f := by
  unfold average
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hf i))

theorem average_square_lower {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    (average f)^2 ≤ average (fun i => (f i)^2) := by
  have hs := average_nonneg (fun i => sq_nonneg (f i - average f))
  simp only [sub_sq, average_add, average_sub, average_mul_const,
    average_const_mul, average_const] at hs
  nlinarith

theorem average_reynolds (f : S → ℝ) :
    average (reynolds (G := G) f) = average f := by
  unfold reynolds
  rw [average_comm]
  have he (g : G) : average (fun x => f (g • x)) = average f :=
    average_equiv (MulAction.toPerm g) f
  simp only [he, average_const]

theorem haar_coefficient_square (f : S → ℝ) :
    average (fun g : G => coefficient f g) =
      average (fun x => (reynolds (G := G) f x)^2) := by
  simp only [coefficient_eq, average_const_mul]
  rw [← dot_reynolds, dot_reynolds_square]
  simp only [dot, average, pow_two]

/-- Haar duplication probability is at least the square of the one-time mean. -/
theorem haar_mean_square_lower [Nonempty S] (f : S → ℝ) :
    (average f)^2 ≤ average (fun g : G => coefficient f g) := by
  rw [haar_coefficient_square, ← average_reynolds (G := G) f]
  exact average_square_lower _

/-- Ordinary Harris inequality under the uniform law, from mathlib's FKG theorem. -/
theorem uniform_harris [DistribLattice S] [Nonempty S] (f h : S → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Monotone f) (hh : Monotone h) :
    average f * average h ≤ average (fun x => f x * h x) := by
  have hs : (∑ x, f x) * (∑ x, h x) ≤
      (Fintype.card S : ℝ) * ∑ x, f x * h x := by
    simpa using fkg f h (fun _ : S => (1 : ℝ)) (by intro; positivity)
      hf0 hh0 hf hh (by intro; simp)
  have hc : (Fintype.card S : ℝ)⁻¹ * (Fintype.card S : ℝ) = 1 := by
    simp [Fintype.card_ne_zero]
  calc
    _ = ((Fintype.card S : ℝ)⁻¹)^2 * ((∑ x, f x) * (∑ x, h x)) := by
      unfold average
      ring
    _ ≤ ((Fintype.card S : ℝ)⁻¹)^2 *
        ((Fintype.card S : ℝ) * ∑ x, f x * h x) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = ((Fintype.card S : ℝ)⁻¹ * (Fintype.card S : ℝ)) *
        average (fun x => f x * h x) := by unfold average; ring
    _ = _ := by rw [hc, one_mul]

/-- Positive association after sampling one Haar permutation, for increasing
nonnegative functions on a finite distributive lattice with an order-preserving action. -/
theorem haar_positive_association [DistribLattice S] [Nonempty S]
    (hact : ∀ g : G, Monotone (fun x : S => g • x)) (f h : S → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Monotone f) (hh : Monotone h) :
    average (fun g : G => coefficient f g) * average (fun g : G => coefficient h g) ≤
      average (fun g : G => coefficient (fun x => f x * h x) g) := by
  refine (haar_covariance f h).trans (average_mono (fun g => ?_))
  have hfg : Monotone (fun x => f x * f (g • x)) := by
    intro x y hxy
    exact mul_le_mul (hf hxy) (hf (hact g hxy)) (hf0 _) (hf0 _)
  have hhg : Monotone (fun x => h x * h (g • x)) := by
    intro x y hxy
    exact mul_le_mul (hh hxy) (hh (hact g hxy)) (hh0 _) (hh0 _)
  have hs := uniform_harris (fun x => f x * f (g • x))
    (fun x => h x * h (g • x)) (fun x => mul_nonneg (hf0 _) (hf0 _))
    (fun x => mul_nonneg (hh0 _) (hh0 _)) hfg hhg
  unfold coefficient
  convert hs using 1
  congr 1
  funext x
  ring

/-- Real-valued indicator of a finite event. -/
noncomputable def eventIndicator (A : Set S) (x : S) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

omit [Fintype S] in
theorem eventIndicator_nonneg (A : Set S) (x : S) : 0 ≤ eventIndicator A x := by
  classical
  simp only [eventIndicator]
  split_ifs <;> norm_num

omit [Fintype S] in
theorem eventIndicator_monotone [Preorder S] (A : Set S) (hA : IsUpperSet A) :
    Monotone (eventIndicator A) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ A
  · have hy : y ∈ A := hA hxy hx
    simp [eventIndicator, hx, hy]
  · simpa [eventIndicator, hx] using eventIndicator_nonneg A y

omit [Fintype S] in
theorem eventIndicator_inter (A B : Set S) :
    eventIndicator (A ∩ B) = fun x => eventIndicator A x * eventIndicator B x := by
  classical
  funext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [eventIndicator, ha, hb]

/-- Probability of `x ∈ A` and `g • x ∈ A`, with independent uniform `x,g`. -/
noncomputable def duplicateProbability (A : Set S) : ℝ :=
  average (fun g : G => coefficient (eventIndicator A) g)

open scoped Classical in
theorem duplicateProbability_eq (A : Set S) :
    duplicateProbability (G := G) A =
      average (fun g : G => average (fun x =>
        if x ∈ A ∧ g • x ∈ A then (1 : ℝ) else 0)) := by
  classical
  unfold duplicateProbability coefficient
  congr 1
  funext g
  congr 1
  funext x
  by_cases hx : x ∈ A <;> by_cases hgx : g • x ∈ A <;>
    simp [eventIndicator, hx, hgx]

/-- The event form of the finite Haar permutation inequality. -/
theorem haar_event_association [DistribLattice S] [Nonempty S]
    (hact : ∀ g : G, Monotone (fun x : S => g • x)) (A B : Set S)
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    duplicateProbability (G := G) A * duplicateProbability (G := G) B ≤
      duplicateProbability (G := G) (A ∩ B) := by
  unfold duplicateProbability
  rw [eventIndicator_inter]
  exact haar_positive_association hact _ _ (eventIndicator_nonneg A)
    (eventIndicator_nonneg B) (eventIndicator_monotone A hA) (eventIndicator_monotone B hB)

theorem haar_event_square_lower [Nonempty S] (A : Set S) :
    (average (eventIndicator A))^2 ≤ duplicateProbability (G := G) A :=
  haar_mean_square_lower _

section Coordinates

open scoped Classical

variable {I : Type*} [Fintype I] [MulAction G I]

/-- The action induced by permuting coordinates of a Boolean configuration. -/
@[instance_reducible] def coordinateAction : MulAction G (I → Bool) where
  smul g ω i := ω (g⁻¹ • i)
  one_smul ω := by
    change (fun i => ω ((1 : G)⁻¹ • i)) = ω
    funext i
    rw [inv_one, one_smul]
  mul_smul g k ω := by
    change (fun i => ω ((g * k)⁻¹ • i)) = (fun i => ω (k⁻¹ • (g⁻¹ • i)))
    funext i
    rw [mul_inv_rev, mul_smul]

/-- Uniform Bernoulli duplication probability for a coordinate permutation action. -/
noncomputable def coordinateDuplicateProbability (A : Set (I → Bool)) : ℝ :=
  letI := coordinateAction (G := G) (I := I)
  duplicateProbability (G := G) A

/-- Finite Haar permutation inequality on the iid Bernoulli(1/2) cube.
Only the two events' increasingness is assumed; preservation of the order
by coordinate permutations is proved here. -/
theorem coordinate_haar_event_association (A B : Set (I → Bool))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    coordinateDuplicateProbability (G := G) A *
        coordinateDuplicateProbability (G := G) B ≤
      coordinateDuplicateProbability (G := G) (A ∩ B) := by
  let := coordinateAction (G := G) (I := I)
  apply haar_event_association
  · intro g ω η hωη i
    exact hωη (g⁻¹ • i)
  · exact hA
  · exact hB

theorem coordinate_haar_event_square_lower (A : Set (I → Bool)) :
    (average (eventIndicator A))^2 ≤ coordinateDuplicateProbability (G := G) A := by
  let := coordinateAction (G := G) (I := I)
  exact haar_event_square_lower A

end Coordinates

#print axioms haar_covariance
#print axioms haar_event_association
#print axioms coordinate_haar_event_association
#print axioms coordinate_haar_event_square_lower

end ExceptionalTimes.FiniteHaar
