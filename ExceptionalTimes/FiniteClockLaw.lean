import ExceptionalTimes.FiniteClockBridge
import ExceptionalTimes.ClockTruncationLimit

/-!
# From actual finite clock laws to cylinder correlations

The lemmas here are measure-theoretic and finite algebraic bridges. In
particular, passing from joint atom probabilities to an event correlation
is proved rather than made part of a published CTMC input.
-/

open MeasureTheory
open scoped BigOperators Matrix ENNReal Classical

namespace ExceptionalTimes.FiniteClockLaw

open FiniteClockBridge FiniteFractional FiniteGenerator FiniteSpectralEnergy

variable {Ξ Ω : Type*} [MeasurableSpace Ξ] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Any finite-valued event is the disjoint sum of its joint atoms.
Almost-everywhere measurability suffices, so no completeness assumption
on the ambient probability space is needed. -/
theorem paired_event_eq_sum {μ : Measure Ξ} {X Y : Ξ → Ω}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (E : Ω → Prop) :
    μ {ω | E (X ω) ∧ E (Y ω)} =
      ∑ η, ∑ ξ, if E η ∧ E ξ then μ {ω | X ω = η ∧ Y ω = ξ} else 0 := by
  classical
  let A : Ω × Ω → Set Ξ := fun z =>
    {ω | X ω = z.1 ∧ Y ω = z.2 ∧ E z.1 ∧ E z.2}
  have hset : {ω | E (X ω) ∧ E (Y ω)} = ⋃ z, A z := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A]
    constructor
    · intro h
      exact ⟨(X ω, Y ω), rfl, rfl, h⟩
    · rintro ⟨⟨η, ξ⟩, hη, hξ, h⟩
      simpa only [hη, hξ] using h
  have hdis : Pairwise (fun z w => Disjoint (A z) (A w)) := by
    intro z w hzw
    apply Set.disjoint_left.mpr
    intro ω hz hw
    exact hzw (Prod.ext (hz.1.symm.trans hw.1) (hz.2.1.symm.trans hw.2.1))
  have hmeas : ∀ z, NullMeasurableSet (A z) μ := by
    intro z
    by_cases h : E z.1 ∧ E z.2
    · have heq : A z = {ω | X ω = z.1} ∩ {ω | Y ω = z.2} := by
        ext ω
        simp [A, h.1, h.2]
      rw [heq]
      exact (hX.nullMeasurableSet_preimage (measurableSet_singleton z.1)).inter
        (hY.nullMeasurableSet_preimage (measurableSet_singleton z.2))
    · have heq : A z = ∅ := by ext ω; simp [A, h]
      rw [heq]
      exact MeasurableSet.empty.nullMeasurableSet
  rw [hset, measure_iUnion₀ (fun z w h => (hdis h).aedisjoint) hmeas,
    tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases h : E η ∧ E ξ
  · simp [A, h.1, h.2]
  · simp [A, h]

noncomputable def indicatorVector (E : Ω → Prop) : Ω → ℂ :=
  fun η => if E η then 1 else 0

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem uniformQuadraticForm_indicator [DecidableEq Ω]
    (M : Matrix Ω Ω ℂ) (E : Ω → Prop) :
    uniformQuadraticForm M (indicatorVector E) =
      (Fintype.card Ω : ℝ)⁻¹ *
        ∑ η, ∑ ξ, if E η ∧ E ξ then (M η ξ).re else 0 := by
  classical
  unfold uniformQuadraticForm
  congr 1
  simp only [dotProduct, Matrix.mulVec, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases hη : E η <;> by_cases hξ : E ξ <;>
    simp [indicatorVector, hη, hξ]

/-- A nonnegative matrix kernel with the actual uniform initial weight
gives exactly the real uniform quadratic form of an event indicator. -/
theorem paired_event_eq_quadraticForm [DecidableEq Ω]
    {μ : Measure Ξ} {X Y : Ξ → Ω}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (M : Matrix Ω Ω ℂ) (hM : ∀ η ξ, 0 ≤ (M η ξ).re)
    (hlaw : ∀ η ξ, μ {ω | X ω = η ∧ Y ω = ξ} =
      ENNReal.ofReal ((Fintype.card Ω : ℝ)⁻¹ * (M η ξ).re))
    (E : Ω → Prop) :
    μ {ω | E (X ω) ∧ E (Y ω)} =
      ENNReal.ofReal (uniformQuadraticForm M (indicatorVector E)) := by
  classical
  rw [paired_event_eq_sum hX hY, uniformQuadraticForm_indicator,
    Finset.mul_sum]
  rw [ENNReal.ofReal_sum_of_nonneg (fun η _ => by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun ξ _ => by split_ifs; exact hM η ξ; exact le_refl 0))]
  apply Finset.sum_congr rfl
  intro η _
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun ξ _ => by
    apply mul_nonneg (by positivity)
    split_ifs; exact hM η ξ; exact le_refl 0)]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases h : E η ∧ E ξ
  · simp [h, hlaw]
  · simp [h]

end ExceptionalTimes.FiniteClockLaw
