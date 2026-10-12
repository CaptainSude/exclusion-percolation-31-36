import ExceptionalTimes.MatchingDimerLaw

/-!
# Independent finite clock slices

This module works directly with the original finite-dimensional count law.
The probability that a time slice contains more than one retained mark is
quadratic in its length. These are the probability estimates for an Euler
approximation of the literal chronological graphical process.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ExceptionalTimes.FiniteClockSlices

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ξ J : Type*} [MeasurableSpace Ξ] [Fintype J]

structure IndexedTests (J : Type*) where
  edge : J → Sym2 Site
  start : J → ℝ
  finish : J → ℝ
  start_nonneg : ∀ j, 0 ≤ start j
  nonempty : ∀ j, start j < finish j
  disjoint : ∀ i j, i ≠ j → edge i = edge j →
    Disjoint (Set.Ioc (start i) (finish i)) (Set.Ioc (start j) (finish j))

noncomputable def IndexedTests.toClockTests (T : IndexedTests J) :
    ClockTests (Fintype.card J) where
  edge i := T.edge ((Fintype.equivFin J).symm i)
  start i := T.start ((Fintype.equivFin J).symm i)
  finish i := T.finish ((Fintype.equivFin J).symm i)
  start_nonneg _i := T.start_nonneg _
  nonempty _i := T.nonempty _
  disjoint _i _j hij he := T.disjoint _ _
    (fun h => hij ((Fintype.equivFin J).symm.injective h)) he

noncomputable def productMass (mean : J → ℝ) (n : J → ℕ) : ℝ≥0∞ :=
  ∏ j, poissonMass (mean j) (n j)

def CountLaw (μ : Measure Ξ) (N : Ξ → J → ℕ) (mean : J → ℝ) : Prop :=
  ∀ n, μ {ω | N ω = n} = productMass mean n

/-- Reindexing the original law to any finite test family is proved. -/
theorem indexed_count_law {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    {initial : Ξ → Configuration} {clocks : Ξ → ClockField}
    (hlaw : IndependentPoissonInitial μ rate initial clocks) (T : IndexedTests J) :
    CountLaw μ (fun ω j => (clocks ω).markCount (T.edge j) (T.start j) (T.finish j))
      (fun j => rate (T.edge j) * (T.finish j - T.start j)) := by
  intro n
  have h := hlaw ∅ (fun _ => false) (Fintype.card J) T.toClockTests
    (fun i => n ((Fintype.equivFin J).symm i))
  have he : {ω | (fun j => (clocks ω).markCount (T.edge j) (T.start j) (T.finish j)) = n} =
      {ω | (∀ v ∈ (∅ : Finset Site), initial ω v = false) ∧
        ∀ i, (clocks ω).markCount (T.toClockTests.edge i)
          (T.toClockTests.start i) (T.toClockTests.finish i) =
            n ((Fintype.equivFin J).symm i)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
      true_and, funext_iff, IndexedTests.toClockTests]
    exact ((Fintype.equivFin J).symm.forall_congr_right).symm
  rw [he, h]
  simp only [Finset.card_empty, pow_zero, one_mul, IndexedTests.toClockTests, productMass]
  exact (Fintype.equivFin J).symm.prod_comp
    (fun j => poissonMass (rate (T.edge j) * (T.finish j - T.start j)) (n j))

theorem indexed_joint_count_law {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    {initial : Ξ → Configuration} {clocks : Ξ → ClockField}
    (hlaw : IndependentPoissonInitial μ rate initial clocks) (V : Finset Site)
    (η : V → Bool) (T : IndexedTests J) (n : J → ℕ) :
    μ {ω | FiniteClockBridge.restrictColor V (initial ω) = η ∧
      (fun j => (clocks ω).markCount (T.edge j) (T.start j) (T.finish j)) = n} =
      (1 / 2 : ℝ≥0∞) ^ V.card *
        productMass (fun j => rate (T.edge j) * (T.finish j - T.start j)) n := by
  have h := FiniteClockBridge.finiteCube_joint_counts V hlaw η (Fintype.card J)
    T.toClockTests (fun i => n ((Fintype.equivFin J).symm i))
  have he : {ω | FiniteClockBridge.restrictColor V (initial ω) = η ∧
      (fun j => (clocks ω).markCount (T.edge j) (T.start j) (T.finish j)) = n} =
      {ω | FiniteClockBridge.restrictColor V (initial ω) = η ∧
        ∀ i, (clocks ω).markCount (T.toClockTests.edge i)
          (T.toClockTests.start i) (T.toClockTests.finish i) =
            n ((Fintype.equivFin J).symm i)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, funext_iff, IndexedTests.toClockTests]
    apply and_congr_right
    intro _
    exact ((Fintype.equivFin J).symm.forall_congr_right).symm
  rw [he, h]
  congr 1
  exact (Fintype.equivFin J).symm.prod_comp
    (fun j => poissonMass (rate (T.edge j) * (T.finish j - T.start j)) (n j))

noncomputable def gridTests {I : Type*} (edge : I → Sym2 Site)
    (hinj : Function.Injective edge) (n : ℕ) (h : ℝ) (hh : 0 < h) :
    IndexedTests (Fin n × I) where
  edge j := edge j.2
  start j := (j.1.val : ℝ) * h
  finish j := ((j.1.val : ℝ) + 1) * h
  start_nonneg j := mul_nonneg (Nat.cast_nonneg _) hh.le
  nonempty j := by nlinarith
  disjoint i j hij he := by
    have heq : i.2 = j.2 := hinj he
    have hs : i.1.val ≠ j.1.val := by
      intro hs
      exact hij (Prod.ext (Fin.ext hs) heq)
    rcases lt_or_gt_of_ne hs with hs | hs
    · apply Set.disjoint_left.mpr
      intro r hi hj
      have hle : (i.1.val : ℝ) + 1 ≤ j.1.val := by exact_mod_cast hs
      have := mul_le_mul_of_nonneg_right hle hh.le
      exact (not_lt_of_ge (le_trans hi.2 this)) hj.1
    · apply Set.disjoint_left.mpr
      intro r hi hj
      have hle : (j.1.val : ℝ) + 1 ≤ i.1.val := by exact_mod_cast hs
      have := mul_le_mul_of_nonneg_right hle hh.le
      exact (not_lt_of_ge (le_trans hj.2 this)) hi.1

theorem grid_count_law {I : Type*} [Fintype I]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    {initial : Ξ → Configuration} {clocks : Ξ → ClockField}
    (hlaw : IndependentPoissonInitial μ rate initial clocks)
    (edge : I → Sym2 Site) (hinj : Function.Injective edge)
    (n : ℕ) (h : ℝ) (hh : 0 < h) :
    CountLaw μ (fun ω (j : Fin n × I) => (clocks ω).markCount (edge j.2)
      ((j.1.val : ℝ) * h) (((j.1.val : ℝ) + 1) * h))
      (fun j => rate (edge j.2) * h) := by
  have hT := indexed_count_law hlaw (gridTests edge hinj n h hh)
  have he : (fun j : Fin n × I => rate ((gridTests edge hinj n h hh).edge j) *
      ((gridTests edge hinj n h hh).finish j - (gridTests edge hinj n h hh).start j)) =
      (fun j => rate (edge j.2) * h) := by
    funext j
    simp only [gridTests]
    ring
  rwa [he] at hT

theorem productMass_zero (mean : J → ℝ) :
    productMass mean 0 = ENNReal.ofReal (Real.exp (-(∑ j, mean j))) := by
  unfold productMass poissonMass
  simp only [Pi.zero_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]

theorem productMass_single [DecidableEq J] (mean : J → ℝ) (hm : ∀ j, 0 ≤ mean j) (i : J) :
    productMass mean (Pi.single i 1) =
      ENNReal.ofReal (Real.exp (-(∑ j, mean j)) * mean i) := by
  have he (j : J) : poissonMass (mean j) ((Pi.single i 1 : J → ℕ) j) =
      ENNReal.ofReal (Real.exp (-mean j) * (if j = i then mean j else 1)) := by
    by_cases hj : j = i <;> simp [poissonMass, hj]
  simp only [productMass, he]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => mul_nonneg (Real.exp_pos _).le
      (by split_ifs; exact hm j; norm_num)),
    Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
  simp

/-- At most one retained mark in the slice, expressed purely in count data. -/
def GoodCounts [DecidableEq J] (N : J → ℕ) : Prop :=
  N = 0 ∨ ∃ i, N = Pi.single i 1

omit [Fintype J] in
theorem single_injective [DecidableEq J] : Function.Injective (fun i : J => Pi.single i (1 : ℕ)) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [hij] at hi

theorem good_probability [DecidableEq J] {μ : Measure Ξ} {N : Ξ → J → ℕ}
    (hN : Measurable N) (mean : J → ℝ) (hm : ∀ j, 0 ≤ mean j)
    (hlaw : CountLaw μ N mean) :
    μ {ω | GoodCounts (N ω)} =
      ENNReal.ofReal (Real.exp (-(∑ j, mean j)) * (1 + ∑ j, mean j)) := by
  have hset : {ω | GoodCounts (N ω)} = {ω | N ω = 0} ∪ ⋃ i, {ω | N ω = Pi.single i 1} := by
    ext ω
    simp [GoodCounts]
  have hdis : Disjoint {ω | N ω = 0} (⋃ i, {ω | N ω = Pi.single i 1}) := by
    apply Set.disjoint_left.mpr
    intro ω h0 hi
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hi
    have h := congrFun (h0.symm.trans hi) i
    simp at h
  have hpair : Pairwise (fun i j => Disjoint {ω | N ω = Pi.single i 1}
      {ω | N ω = Pi.single j 1}) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (single_injective (hi.symm.trans hj))
  have hmeas (a : J → ℕ) : MeasurableSet {ω | N ω = a} :=
    hN (measurableSet_singleton a)
  rw [hset, measure_union hdis (MeasurableSet.iUnion (fun i => hmeas _)),
    measure_iUnion hpair (fun i => hmeas _), tsum_fintype, hlaw 0, productMass_zero]
  have hsum : (∑ i, μ {ω | N ω = Pi.single i 1}) =
      ∑ i, ENNReal.ofReal (Real.exp (-(∑ j, mean j)) * mean i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hlaw _).trans (productMass_single mean hm i)
  rw [hsum]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Real.exp_pos _).le (hm i)),
    ← ENNReal.ofReal_add (Real.exp_pos _).le
      (Finset.sum_nonneg (fun i _ => mul_nonneg (Real.exp_pos _).le (hm i))),
    ← Finset.mul_sum]
  congr 1
  ring

/-- The probability of two or more retained marks is quadratic in the
total Poisson mean. The constant is uniform in the number of clocks. -/
theorem bad_probability_le [DecidableEq J] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {N : Ξ → J → ℕ} (hN : Measurable N) (mean : J → ℝ) (hm : ∀ j, 0 ≤ mean j)
    (hlaw : CountLaw μ N mean) :
    μ {ω | ¬ GoodCounts (N ω)} ≤ ENNReal.ofReal ((∑ j, mean j) ^ 2) := by
  have hs : 0 ≤ ∑ j, mean j := Finset.sum_nonneg (fun j _ => hm j)
  have hmeas : MeasurableSet {ω | GoodCounts (N ω)} := by
    exact hN (MeasurableSet.of_discrete : MeasurableSet {n | GoodCounts n})
  change μ {ω | GoodCounts (N ω)}ᶜ ≤ _
  rw [prob_compl_eq_one_sub hmeas, good_probability hN mean hm hlaw,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1
      (mul_nonneg (Real.exp_pos _).le (by linarith))]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg (∑ j, mean j))
    (show 0 ≤ 1 + ∑ j, mean j by linarith)
  nlinarith

#print axioms grid_count_law
#print axioms bad_probability_le

noncomputable def sliceTests (edge : J → Sym2 Site) (hinj : Function.Injective edge)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < h) : IndexedTests J where
  edge := edge
  start _ := a
  finish _ := a + h
  start_nonneg _ := ha
  nonempty _ := by linarith
  disjoint i j hij he := (hij (hinj he)).elim

theorem slice_count_law {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    {initial : Ξ → Configuration} {clocks : Ξ → ClockField}
    (hlaw : IndependentPoissonInitial μ rate initial clocks)
    (edge : J → Sym2 Site) (hinj : Function.Injective edge)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < h) :
    CountLaw μ (fun ω j => (clocks ω).markCount (edge j) a (a + h))
      (fun j => rate (edge j) * h) := by
  simpa only [sliceTests, add_sub_cancel_left] using
    indexed_count_law hlaw (sliceTests edge hinj a h ha hh)

theorem any_bad_probability_le [DecidableEq J] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    (n : ℕ) (N : Ξ → Fin n → J → ℕ) (hN : ∀ j, Measurable (fun ω => N ω j))
    (mean : J → ℝ) (hm : ∀ i, 0 ≤ mean i)
    (hlaw : ∀ j, CountLaw μ (fun ω => N ω j) mean) :
    μ {ω | ∃ j, ¬ GoodCounts (N ω j)} ≤
      (n : ℝ≥0∞) * ENNReal.ofReal ((∑ i, mean i) ^ 2) := by
  have he : {ω | ∃ j, ¬ GoodCounts (N ω j)} = ⋃ j, {ω | ¬ GoodCounts (N ω j)} := by
    ext ω
    simp
  rw [he]
  calc
    _ ≤ ∑ j : Fin n, μ {ω | ¬ GoodCounts (N ω j)} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal ((∑ i, mean i) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact bad_probability_le (hN j) mean hm (hlaw j)
    _ = _ := by simp

theorem graphical_grid_bad_probability_le [DecidableEq J]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : J → Sym2 Site)
    (hinj : Function.Injective edge) (hrate : ∀ j, 0 ≤ rate (edge j))
    (n : ℕ) (h : ℝ) (hh : 0 < h) :
    μ {ω | ∃ j : Fin n, ¬ GoodCounts
      (fun i => (P.clocks ω).markCount (edge i) ((j.val : ℝ) * h)
        (((j.val : ℝ) + 1) * h))} ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (((∑ i, rate (edge i)) * h) ^ 2) := by
  let _ : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  have hb := any_bad_probability_le n
    (fun ω j i => (P.clocks ω).markCount (edge i) ((j.val : ℝ) * h)
      (((j.val : ℝ) + 1) * h))
    (fun j => Measurable.of_eval (fun i => P.measurable_counts _ _ _))
    (fun i => rate (edge i) * h) (fun i => mul_nonneg (hrate i) hh.le)
    (fun j => by
      have hL := slice_count_law P.independent_law edge hinj ((j.val : ℝ) * h) h
        (mul_nonneg (Nat.cast_nonneg _) hh.le) hh
      simpa only [add_mul, one_mul] using hL)
  simpa only [← Finset.sum_mul] using hb

#print axioms graphical_grid_bad_probability_le

end ExceptionalTimes.FiniteClockSlices
