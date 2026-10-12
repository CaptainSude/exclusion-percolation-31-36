import ExceptionalTimes.FiniteClockMarginal

/-! A finite clock state is uniform and independent of every future
finite family of disjoint clock counts. This is proved from the actual
count cylinder law by erasing the finite random permutation of the past. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical Topology

namespace ExceptionalTimes.FiniteClockFutureLaw

open FiniteClockWordLaw FiniteClockBridge FiniteClockGridLaw FiniteClockSlices
open FiniteClockMarginal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem uniform_random_bijection_joint {Ω S K L : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace K] [MeasurableSingletonClass K] [Countable K]
    [MeasurableSpace L] [MeasurableSingletonClass L]
    {μ : Measure Ω} (X : Ω → S) (W : Ω → K) (Y : Ω → L)
    (hX : Measurable X) (hW : Measurable W) (hY : Measurable Y)
    (U : K → S → S) (hU : ∀ k, Function.Bijective (U k))
    (a : ℝ≥0∞) (p : K → ℝ≥0∞) (q : L → ℝ≥0∞) (hp : ∑' k, p k = 1)
    (hlaw : ∀ x k l, μ {ω | X ω = x ∧ W ω = k ∧ Y ω = l} = a * p k * q l)
    (y : S) (l : L) :
    μ {ω | U (W ω) (X ω) = y ∧ Y ω = l} = a * q l := by
  let e (k : K) := Equiv.ofBijective (U k) (hU k)
  let A (k : K) : Set Ω := {ω | X ω = (e k).symm y ∧ W ω = k ∧ Y ω = l}
  have hset : {ω | U (W ω) (X ω) = y ∧ Y ω = l} = ⋃ k, A k := by
    ext ω
    constructor
    · rintro ⟨h,hl⟩
      refine mem_iUnion.mpr ⟨W ω,?_,rfl,hl⟩
      apply (e (W ω)).injective
      simpa [e] using h
    · intro h
      obtain ⟨k,hx,hw,hl⟩ := mem_iUnion.mp h
      refine ⟨?_,hl⟩
      rw [hw,hx]
      exact (e k).apply_symm_apply y
  have hdis : Pairwise (fun j k => Disjoint (A j) (A k)) := by
    intro j k hne
    exact Set.disjoint_left.mpr (fun _ hj hk => hne (hj.2.1.symm.trans hk.2.1))
  have hmeas (k : K) : MeasurableSet (A k) :=
    (hX (measurableSet_singleton ((e k).symm y))).inter
      ((hW (measurableSet_singleton k)).inter (hY (measurableSet_singleton l)))
  rw [hset,measure_iUnion hdis hmeas]
  calc
    (∑' k, μ (A k)) = ∑' k, a * p k * q l := tsum_congr (fun k => hlaw _ k l)
    _ = a * q l := by rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left,hp,mul_one]

theorem measure_event_le_of_discrepancy_aux {Ω S T : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : Ω → T) (Y Z : Ω → S) (E : T → S → Prop) :
    μ {ω | E (X ω) (Y ω)} ≤ μ {ω | E (X ω) (Z ω)} + μ {ω | Y ω ≠ Z ω} := by
  apply le_trans (measure_mono (t := {ω | E (X ω) (Z ω)} ∪ {ω | Y ω ≠ Z ω}) ?_)
    (measure_union_le _ _)
  intro ω hω
  change E (X ω) (Y ω) at hω
  by_cases he : Y ω = Z ω
  · exact Or.inl (by change E (X ω) (Z ω); simpa only [← he] using hω)
  · exact Or.inr he

theorem event_probability_eq_of_approximation_aux {Ω S T : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : Ω → T) (Y : Ω → S) (Z : ℕ → Ω → S)
    (E : T → S → Prop) {p : ℝ≥0∞}
    (hp : Tendsto (fun n => μ {ω | E (X ω) (Z n ω)}) atTop (𝓝 p))
    (he : Tendsto (fun n => μ {ω | Y ω ≠ Z n ω}) atTop (𝓝 0)) :
    μ {ω | E (X ω) (Y ω)} = p := by
  apply le_antisymm
  · simpa only [add_zero] using ge_of_tendsto (hp.add he)
      (Eventually.of_forall (fun n => measure_event_le_of_discrepancy_aux X Y (Z n) E))
  · have hle : ∀ n, μ {ω | E (X ω) (Z n ω)} ≤
        μ {ω | E (X ω) (Y ω)} + μ {ω | Y ω ≠ Z n ω} := by
      intro n
      simpa only [ne_comm] using measure_event_le_of_discrepancy_aux X (Z n) Y E
    simpa only [add_zero] using le_of_tendsto_of_tendsto hp (tendsto_const_nhds.add he)
      (Eventually.of_forall hle)

def appendTests {J K : Type*} (T : IndexedTests J) (U : IndexedTests K)
    {s : ℝ} (hT : ∀ j, T.finish j ≤ s) (hU : ∀ k, s ≤ U.start k) :
    IndexedTests (J ⊕ K) where
  edge := Sum.elim T.edge U.edge
  start := Sum.elim T.start U.start
  finish := Sum.elim T.finish U.finish
  start_nonneg := Sum.rec T.start_nonneg U.start_nonneg
  nonempty := Sum.rec T.nonempty U.nonempty
  disjoint i j hij he := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact T.disjoint i j (fun h => hij (congrArg Sum.inl h)) he
      | inr j =>
        exact Set.disjoint_left.mpr (fun _ hi hj =>
          (not_lt_of_ge (hi.2.trans ((hT i).trans (hU j)))) hj.1)
    | inr i =>
      cases j with
      | inl j =>
        exact Set.disjoint_left.mpr (fun _ hi hj =>
          (not_lt_of_ge (hj.2.trans ((hT j).trans (hU i)))) hi.1)
      | inr j => exact U.disjoint i j (fun h => hij (congrArg Sum.inr h)) he

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I] [Fintype J]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ}

omit [DecidableEq I] in
theorem joint_past_future_count_law (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (T : IndexedTests I) (U : IndexedTests J)
    {s : ℝ} (hT : ∀ i, T.finish i ≤ s) (hU : ∀ j, s ≤ U.start j)
    (η : V → Bool) (m : I → ℕ) (n : J → ℕ) :
    μ {ω | restrictColor V (P.initial ω) = η ∧
      (fun i => (P.clocks ω).markCount (T.edge i) (T.start i) (T.finish i)) = m ∧
      (fun j => (P.clocks ω).markCount (U.edge j) (U.start j) (U.finish j)) = n} =
      (1/2 : ℝ≥0∞)^V.card *
        productMass (fun i => rate (T.edge i)*(T.finish i-T.start i)) m *
        productMass (fun j => rate (U.edge j)*(U.finish j-U.start j)) n := by
  have H := indexed_joint_count_law P.independent_law V η (appendTests T U hT hU) (Sum.elim m n)
  have he (ω : Ω) : (fun i : I ⊕ J => (P.clocks ω).markCount
      ((appendTests T U hT hU).edge i) ((appendTests T U hT hU).start i)
      ((appendTests T U hT hU).finish i)) = Sum.elim m n ↔
      (fun i => (P.clocks ω).markCount (T.edge i) (T.start i) (T.finish i)) = m ∧
        (fun j => (P.clocks ω).markCount (U.edge j) (U.start j) (U.finish j)) = n := by
    simp only [funext_iff,Sum.forall,appendTests,Sum.elim_inl,Sum.elim_inr]
  simp_rw [he] at H
  simpa only [productMass,Fintype.prod_sum_type,appendTests,Sum.elim_inl,Sum.elim_inr,
    mul_assoc] using H

#print axioms uniform_random_bijection_joint
#print axioms joint_past_future_count_law




omit [DecidableEq I] in
theorem grid_joint_future_count_law (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (n : ℕ) (h : ℝ) (hh : 0 < h) (U : IndexedTests J)
    (hU : ∀ j, (n : ℝ)*h ≤ U.start j) (η : V → Bool)
    (w : Fin n → I → ℕ) (m : J → ℕ) :
    μ {ω | restrictColor V (P.initial ω) = η ∧
      gridWord (P.clocks ω) (siteEdges V edge) h n = w ∧
      (fun j => (P.clocks ω).markCount (U.edge j) (U.start j) (U.finish j)) = m} =
      (1/2 : ℝ≥0∞)^V.card *
        (∏ j, productMass (fun i => rate (edgePair V edge i)*h) (w j)) *
        productMass (fun j => rate (U.edge j)*(U.finish j-U.start j)) m := by
  have hT (j : Fin n × I) : (gridTests (edgePair V edge) hinj n h hh).finish j ≤ (n : ℝ)*h := by
    apply mul_le_mul_of_nonneg_right _ hh.le
    exact_mod_cast j.1.isLt
  have H := joint_past_future_count_law P V (gridTests (edgePair V edge) hinj n h hh)
    U hT hU η (fun ji => w ji.1 ji.2) m
  have hmean : (fun ji : Fin n × I => rate ((gridTests (edgePair V edge) hinj n h hh).edge ji) *
      ((gridTests (edgePair V edge) hinj n h hh).finish ji -
        (gridTests (edgePair V edge) hinj n h hh).start ji)) =
      (fun ji => rate (edgePair V edge ji.2)*h) := by
    funext ji
    dsimp [gridTests]
    ring
  rw [hmean] at H
  simpa only [gridWord,FiniteClockSlicePath.sliceCounts,FiniteClockSlicePath.pairIndex,
    siteEdges,edgePair,gridTests,productMass,Fintype.prod_prod_type,funext_iff,Prod.forall] using H

theorem grid_uniform_future_counts (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (n : ℕ) (h : ℝ) (hh : 0 < h) (U : IndexedTests J)
    (hU : ∀ j, (n : ℝ)*h ≤ U.start j) (η : V → Bool) (m : J → ℕ) :
    μ {ω | gridApprox V P edge h n ω = η ∧
      (fun j => (P.clocks ω).markCount (U.edge j) (U.start j) (U.finish j)) = m} =
      (1/2 : ℝ≥0∞)^V.card *
        productMass (fun j => rate (U.edge j)*(U.finish j-U.start j)) m := by
  apply uniform_random_bijection_joint (fun ω => restrictColor V (P.initial ω))
    (fun ω => gridWord (P.clocks ω) (siteEdges V edge) h n)
    (fun ω j => (P.clocks ω).markCount (U.edge j) (U.start j) (U.finish j))
    (Measurable.of_eval (fun v => (measurable_pi_apply (v : Site)).comp P.measurable_initial))
    (measurable_gridWord V P edge h n)
    (Measurable.of_eval (fun j => P.measurable_counts _ _ _))
    (runWord (cubeUpdate V edge)) (runWord_bijective _ (cubeUpdate_bijective V edge) n)
    _ (fun w => ∏ j, productMass (fun i => rate (edgePair V edge i)*h) (w j))
    (productMass (fun j => rate (U.edge j)*(U.finish j-U.start j)))
  · rw [tsum_fin_product]
    simp [productMass_sum _ (fun i => mul_nonneg (hr i) hh.le)]
  · exact grid_joint_future_count_law P V edge hinj n h hh U hU

/-- The literal finite graphical configuration at time s is independent
of all later count tests. No transition-kernel or Markov assumption is
added to the count-cylinder model. -/
theorem projected_uniform_future_counts (P : PoissonGraphicalRealization μ rate)
    (V : Finset Site) (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (s : ℝ) (hs : 0 < s) (U : IndexedTests J)
    (hU : ∀ j, s ≤ U.start j) (η : V → Bool) (m : J → ℕ) :
    μ {ω | projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
        edge (P.initial ω) s = η ∧
      (fun j => (P.clocks ω).markCount (U.edge j) (U.start j) (U.finish j)) = m} =
      (1/2 : ℝ≥0∞)^V.card *
        productMass (fun j => rate (U.edge j)*(U.finish j-U.start j)) m := by
  apply event_probability_eq_of_approximation_aux
    (fun ω j => (P.clocks ω).markCount (U.edge j) (U.start j) (U.finish j))
    (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) s)
    (fun n => gridApprox V P edge (s/n) n) (fun c x => x = η ∧ c = m)
  · apply tendsto_atTop_of_eventually_const (i₀ := 1)
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply grid_uniform_future_counts P V edge hinj hr n (s/n) (div_pos hs hn') U
    intro j
    simpa only [mul_div_cancel₀ s hn'.ne'] using hU j
  · exact tendsto_projected_discrepancy V P edge hinj hr s hs

#print axioms grid_uniform_future_counts
#print axioms projected_uniform_future_counts

end ExceptionalTimes.FiniteClockFutureLaw
