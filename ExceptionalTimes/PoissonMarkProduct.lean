import ExceptionalTimes.StochasticModel
import Mathlib.Probability.ProductMeasure

/-! Locally finite positive point sets, their count sigma-algebra, and the
finite count law of a product of independent point-set laws. Existence of
any one-coordinate Poisson law is not asserted in this module. -/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ExceptionalTimes

structure PositiveMarks where
  marks : Set ℝ
  positive : ∀ t ∈ marks, 0 < t
  finite : ∀ a b, (marks ∩ Ioc a b).Finite

namespace PositiveMarks

noncomputable def count (M : PositiveMarks) (a b : ℝ) : ℕ :=
  (M.marks ∩ Ioc a b).ncard

noncomputable def countMap (M : PositiveMarks) (p : ℝ × ℝ) : ℕ := M.count p.1 p.2

noncomputable instance : MeasurableSpace PositiveMarks :=
  MeasurableSpace.comap countMap inferInstance

theorem measurable_count (a b : ℝ) : Measurable (fun M : PositiveMarks => M.count a b) :=
  (measurable_pi_apply (a,b)).comp (comap_measurable countMap)

def empty : PositiveMarks where
  marks := ∅
  positive _ h := h.elim
  finite _ _ := by simp

@[simp] theorem count_empty (a b : ℝ) : empty.count a b = 0 := by simp [count,empty]

/-- The ordinary finite disjoint-interval count formula for one point set.
The family is finite; its intervals all lie in the positive time half-line. -/
def HasPoissonCounts (ν : Measure PositiveMarks) (rate : ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] (a b : I → ℝ) (n : I → ℕ),
    (∀ i, 0 ≤ a i) → (∀ i, a i < b i) →
    (∀ i j, i ≠ j → Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) →
    ν {M | ∀ i, M.count (a i) (b i) = n i} =
      ∏ i, poissonMass (rate * (b i-a i)) (n i)

theorem measurableSet_count_constraints {I : Type*} [Countable I]
    (a b : I → ℝ) (n : I → ℕ) :
    MeasurableSet {M : PositiveMarks | ∀ i, M.count (a i) (b i) = n i} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => measurable_count (a i) (b i)
    (measurableSet_singleton (n i))

theorem empty_hasPoissonCounts : HasPoissonCounts (Measure.dirac empty) 0 := by
  intro I _ a b n _ _ _
  rw [Measure.dirac_apply' empty (measurableSet_count_constraints a b n)]
  by_cases hn : ∀ i, n i = 0
  · simp [hn,poissonMass]
  · obtain ⟨i,hi⟩ := not_forall.mp hn
    have hmem : empty ∉ {M : PositiveMarks | ∀ j, M.count (a j) (b j) = n j} := by
      intro h
      exact hi ((count_empty (a i) (b i)).symm.trans (h i)).symm
    rw [Set.indicator_of_notMem hmem]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [poissonMass,hi]

theorem product_count_law {J : Type*} (ν : J → Measure PositiveMarks)
    [∀ j, IsProbabilityMeasure (ν j)] (rate : J → ℝ)
    (hlaw : ∀ j, HasPoissonCounts (ν j) (rate j))
    (I : Type) [Fintype I] (edge : I → J) (a b : I → ℝ) (n : I → ℕ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → edge i = edge j →
      Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) :
    Measure.infinitePi ν {ω | ∀ i, (ω (edge i)).count (a i) (b i) = n i} =
      ∏ i, poissonMass (rate (edge i) * (b i-a i)) (n i) := by
  let S : Finset J := Finset.univ.image edge
  let E : J → Set PositiveMarks := fun j =>
    {M | ∀ i, edge i = j → M.count (a i) (b i) = n i}
  have hE : ∀ j, MeasurableSet (E j) := by
    intro j
    simp only [E,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact MeasurableSet.iInter fun _ => measurable_count (a i) (b i)
      (measurableSet_singleton (n i))
  have hevent : {ω : J → PositiveMarks | ∀ i, (ω (edge i)).count (a i) (b i) = n i} =
      (S : Set J).pi E := by
    ext ω
    constructor
    · intro h j _ i hi
      simpa only [← hi] using h i
    · intro h i
      exact h (edge i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) i rfl
  rw [hevent,Measure.infinitePi_pi ν (fun j _ => hE j)]
  have hfiber (j : J) : ν j (E j) =
      ∏ i ∈ Finset.univ with edge i = j,
        poissonMass (rate (edge i) * (b i-a i)) (n i) := by
    let T : Finset I := Finset.univ.filter (fun i => edge i = j)
    have hT : ∀ i : T, edge i.val = j := fun i => (Finset.mem_filter.mp i.property).2
    have H := hlaw j T (fun i => a i.val) (fun i => b i.val) (fun i => n i.val)
      (fun i => ha i.val) (fun i => hab i.val)
      (fun i l hil => hdisj i.val l.val (fun h => hil (Subtype.ext h))
        ((hT i).trans (hT l).symm))
    have hset : {M : PositiveMarks | ∀ i : T, M.count (a i.val) (b i.val) = n i.val} = E j := by
      ext M
      constructor
      · intro h i hi
        exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
      · intro h i
        exact h i.val (hT i)
    rw [hset] at H
    rw [H]
    change (∏ i : T, poissonMass (rate j * (b i.val-a i.val)) (n i.val)) =
      ∏ i ∈ T, poissonMass (rate (edge i) * (b i-a i)) (n i)
    rw [← Finset.prod_coe_sort T]
    exact Finset.prod_congr rfl fun i _ => by rw [hT i]
  simp_rw [hfiber]
  exact Finset.prod_fiberwise_of_maps_to
    (fun i _ => Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩) _

#print axioms product_count_law

end PositiveMarks
end ExceptionalTimes
