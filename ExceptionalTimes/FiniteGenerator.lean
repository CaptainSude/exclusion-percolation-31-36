import ExceptionalTimes.FiniteHaar
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Actual finite swap generators and their Dirichlet forms

The generator below is a finite weighted sum of the literal state-space
permutations induced by exchanging two colors. Its matrix action, symmetry,
uniform-law energy identity and rate comparison are finite algebraic facts.
No probabilistic semigroup identification or C-star-algebra instance is
postulated. The sign convention is the positive generator `L = -Q`.
-/

open scoped BigOperators Matrix
open ExceptionalTimes.FiniteHaar

namespace ExceptionalTimes.FiniteGenerator

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

noncomputable def generator (σ : I → Equiv.Perm Ω) (rate : I → ℝ)
    (f : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, rate i * (f ω - f (σ i ω))

omit [Fintype Ω] in
theorem generator_const (σ : I → Equiv.Perm Ω) (rate : I → ℝ) (c : ℝ) :
    generator σ rate (fun _ => c) = 0 := by
  funext ω
  simp [generator]

omit [Fintype Ω] in
theorem generator_sub_rates (σ : I → Equiv.Perm Ω) (r s : I → ℝ) (f : Ω → ℝ) :
    generator σ (fun i => s i - r i) f =
      generator σ s f - generator σ r f := by
  funext ω
  simp [generator, sub_mul, Finset.sum_sub_distrib]

theorem sum_involution_swap (σ : Equiv.Perm Ω) (hσ : Function.Involutive σ)
    (f g : Ω → ℝ) :
    (∑ ω, f (σ ω) * g ω) = ∑ ω, f ω * g (σ ω) := by
  calc
    (∑ ω, f (σ ω) * g ω) = ∑ ω, f (σ ω) * g (σ (σ ω)) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [hσ ω]
    _ = _ := Equiv.sum_comp σ (fun ω => f ω * g (σ ω))

theorem single_edge_bilinear (σ : Equiv.Perm Ω) (hσ : Function.Involutive σ)
    (f g : Ω → ℝ) :
    (∑ ω, f ω * (g ω - g (σ ω))) =
      (1 / 2 : ℝ) * ∑ ω, (f ω - f (σ ω)) * (g ω - g (σ ω)) := by
  have hcross := sum_involution_swap σ hσ f g
  have hsame : (∑ ω, f (σ ω) * g (σ ω)) = ∑ ω, f ω * g ω :=
    Equiv.sum_comp σ (fun ω => f ω * g ω)
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib] at *
  linarith

/-- Bilinear reversibility/Dirichlet identity with unordered-edge factor 1/2. -/
theorem sum_generator_bilinear (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ) (f g : Ω → ℝ) :
    (∑ ω, f ω * generator σ rate g ω) =
      (1 / 2 : ℝ) * ∑ i, rate i *
        ∑ ω, (f ω - f (σ i ω)) * (g ω - g (σ i ω)) := by
  simp only [generator, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ ω, f ω * (rate i * (g ω - g (σ i ω)))) =
        rate i * ∑ ω, f ω * (g ω - g (σ i ω)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by
      rw [single_edge_bilinear _ (hσ i)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

theorem sum_generator_symmetric (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ) (f g : Ω → ℝ) :
    (∑ ω, f ω * generator σ rate g ω) = ∑ ω, g ω * generator σ rate f ω := by
  rw [sum_generator_bilinear σ hσ, sum_generator_bilinear σ hσ]
  simp only [mul_comm]

/-- The inner product is normalized by the actual uniform state law. -/
theorem average_generator_energy (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ) (f : Ω → ℝ) :
    average (fun ω => f ω * generator σ rate f ω) =
      (1 / 2 : ℝ) * ∑ i, rate i * average (fun ω => (f ω - f (σ i ω)) ^ 2) := by
  unfold average
  rw [sum_generator_bilinear σ hσ]
  simp only [pow_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sum_generator_nonneg (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ)
    (hr : ∀ i, 0 ≤ rate i) (f : Ω → ℝ) :
    0 ≤ ∑ ω, f ω * generator σ rate f ω := by
  rw [sum_generator_bilinear σ hσ]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hr i)
    (Finset.sum_nonneg (fun ω _ => mul_self_nonneg _)))

theorem average_generator_mono (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) {r s : I → ℝ}
    (hrs : ∀ i, r i ≤ s i) (f : Ω → ℝ) :
    average (fun ω => f ω * generator σ r f ω) ≤
      average (fun ω => f ω * generator σ s f ω) := by
  rw [average_generator_energy σ hσ, average_generator_energy σ hσ]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right (hrs i)
  unfold average
  positivity

section Matrix

variable [DecidableEq Ω]

/-- The literal `I - U` matrix for a state permutation. -/
noncomputable def jumpMatrix (σ : Equiv.Perm Ω) : Matrix Ω Ω ℝ :=
  fun ω η => (if ω = η then 1 else 0) - (if σ ω = η then 1 else 0)

noncomputable def generatorMatrix (σ : I → Equiv.Perm Ω) (rate : I → ℝ) :
    Matrix Ω Ω ℝ := fun ω η => ∑ i, rate i * jumpMatrix (σ i) ω η

theorem jumpMatrix_mulVec (σ : Equiv.Perm Ω) (f : Ω → ℝ) :
    jumpMatrix σ *ᵥ f = fun ω => f ω - f (σ ω) := by
  funext ω
  simp [Matrix.mulVec, dotProduct, jumpMatrix, sub_mul,
    Finset.sum_sub_distrib, eq_comm]

theorem generatorMatrix_mulVec (σ : I → Equiv.Perm Ω) (rate : I → ℝ) (f : Ω → ℝ) :
    generatorMatrix σ rate *ᵥ f = generator σ rate f := by
  funext ω
  simp only [Matrix.mulVec, dotProduct, generatorMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold generator
  apply Finset.sum_congr rfl
  intro i _
  have hi := congrFun (jumpMatrix_mulVec (σ i) f) ω
  change (∑ η, jumpMatrix (σ i) ω η * f η) = _ at hi
  rw [← hi]
  simp only [Finset.mul_sum, mul_assoc]

omit [Fintype Ω] in
theorem jumpMatrix_symmetric (σ : Equiv.Perm Ω) (hσ : Function.Involutive σ)
    (ω η : Ω) : jumpMatrix σ ω η = jumpMatrix σ η ω := by
  have he : σ ω = η ↔ σ η = ω := by
    constructor
    · intro h
      rw [← h, hσ]
    · intro h
      rw [← h, hσ]
  simp only [jumpMatrix, he, eq_comm]

omit [Fintype Ω] in
theorem generatorMatrix_symmetric (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ) (ω η : Ω) :
    generatorMatrix σ rate ω η = generatorMatrix σ rate η ω := by
  simp only [generatorMatrix, jumpMatrix_symmetric _ (hσ _) ω η]

omit [Fintype Ω] in
theorem generatorMatrix_isHermitian (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ) :
    (generatorMatrix σ rate).IsHermitian := by
  ext ω η
  simpa only [Matrix.conjTranspose_apply, star_trivial] using
    generatorMatrix_symmetric σ hσ rate η ω

/-- Positive semidefiniteness is proved for the actual generator matrix. -/
theorem generatorMatrix_posSemidef (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) (rate : I → ℝ)
    (hr : ∀ i, 0 ≤ rate i) : (generatorMatrix σ rate).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨generatorMatrix_isHermitian σ hσ rate, ?_⟩
  intro f
  rw [generatorMatrix_mulVec]
  simpa only [dotProduct, star_trivial] using sum_generator_nonneg σ hσ rate hr f

omit [Fintype Ω] in
theorem generatorMatrix_sub_rates (σ : I → Equiv.Perm Ω) (r s : I → ℝ) :
    generatorMatrix σ s - generatorMatrix σ r = generatorMatrix σ (fun i => s i - r i) := by
  ext ω η
  simp [generatorMatrix, sub_mul, Finset.sum_sub_distrib]

/-- This is Loewner domination, expressed without installing an ambiguous
pointwise matrix order instance. -/
theorem generatorMatrix_sub_posSemidef (σ : I → Equiv.Perm Ω)
    (hσ : ∀ i, Function.Involutive (σ i)) {r s : I → ℝ} (hrs : ∀ i, r i ≤ s i) :
    (generatorMatrix σ s - generatorMatrix σ r).PosSemidef := by
  rw [generatorMatrix_sub_rates]
  exact generatorMatrix_posSemidef σ hσ _ (fun i => sub_nonneg.mpr (hrs i))

end Matrix

section ColorSwaps

variable {V : Type*} [DecidableEq V]

/-- A genuine coordinate exchange on the finite color state space. -/
noncomputable def colorSwap (x y : V) : Equiv.Perm (V → Bool) where
  toFun ω := ω ∘ Equiv.swap x y
  invFun ω := ω ∘ Equiv.swap x y
  left_inv ω := by funext v; simp
  right_inv ω := by funext v; simp

theorem colorSwap_involutive (x y : V) : Function.Involutive (colorSwap x y) := by
  intro ω
  funext v
  simp [colorSwap]

theorem colorSwap_apply (x y : V) (ω : V → Bool) (v : V) :
    colorSwap x y ω v = ω (Equiv.swap x y v) := rfl

variable [Fintype V]

/-- Actual color-swap Dirichlet form for an arbitrary finite edge list.
An edge is indexed once; duplicate entries, if supplied, add their rates. -/
theorem colorSwap_generator_energy (edge : I → V × V) (rate : I → ℝ)
    (f : (V → Bool) → ℝ) :
    average (fun ω => f ω * generator (fun i => colorSwap (edge i).1 (edge i).2) rate f ω) =
      (1 / 2 : ℝ) * ∑ i, rate i *
        average (fun ω => (f ω - f (ω ∘ Equiv.swap (edge i).1 (edge i).2)) ^ 2) :=
  average_generator_energy _ (fun _ => colorSwap_involutive _ _) rate f

end ColorSwaps

#print axioms average_generator_energy
#print axioms generatorMatrix_mulVec
#print axioms generatorMatrix_posSemidef
#print axioms generatorMatrix_sub_posSemidef
#print axioms colorSwap_generator_energy

end ExceptionalTimes.FiniteGenerator
