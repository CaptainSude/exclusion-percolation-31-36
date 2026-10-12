import ExceptionalTimes.FiniteClockGridLaw
import ExceptionalTimes.TruncatedMeasurability
import ExceptionalTimes.ClockTruncationAE
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Uniform marginals of the actual finite clock process, proved directly
from the joint independent count law and the grid approximation. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical Topology

namespace ExceptionalTimes.FiniteClockMarginal

theorem uniform_random_bijection {Ω S K : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace K] [MeasurableSingletonClass K] [Countable K]
    {μ : Measure Ω} (X : Ω → S) (W : Ω → K) (hX : Measurable X) (hW : Measurable W)
    (U : K → S → S) (hU : ∀ k, Function.Bijective (U k))
    (a : ℝ≥0∞) (p : K → ℝ≥0∞) (hp : ∑' k, p k = 1)
    (hlaw : ∀ x k, μ {ω | X ω = x ∧ W ω = k} = a * p k) (y : S) :
    μ {ω | U (W ω) (X ω) = y} = a := by
  let e (k : K) := Equiv.ofBijective (U k) (hU k)
  let A (k : K) : Set Ω := {ω | X ω = (e k).symm y ∧ W ω = k}
  have hset : {ω | U (W ω) (X ω) = y} = ⋃ k, A k := by
    ext ω
    constructor
    · intro h
      refine mem_iUnion.mpr ⟨W ω, ?_, rfl⟩
      apply (e (W ω)).injective
      simpa [e] using h
    · intro h
      obtain ⟨k, hx, hw⟩ := mem_iUnion.mp h
      change U (W ω) (X ω) = y
      rw [hw, hx]
      exact (e k).apply_symm_apply y
  have hdis : Pairwise (fun j k => Disjoint (A j) (A k)) := by
    intro j k hne
    exact Set.disjoint_left.mpr (fun _ hj hk => hne (hj.2.symm.trans hk.2))
  have hmeas (k : K) : MeasurableSet (A k) :=
    (hX (measurableSet_singleton ((e k).symm y))).inter (hW (measurableSet_singleton k))
  rw [hset, measure_iUnion hdis hmeas]
  calc
    (∑' k, μ (A k)) = ∑' k, a * p k := tsum_congr (fun k => hlaw _ k)
    _ = a := by rw [ENNReal.tsum_mul_left, hp, mul_one]

open FiniteClockWordLaw FiniteClockBridge FiniteClockGridLaw FiniteClockSlices

theorem tsum_fin_product {K : Type*} (n : ℕ) (f : Fin n → K → ℝ≥0∞) :
    (∑' w : Fin n → K, ∏ j, f j (w j)) = ∏ j, ∑' k, f j k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => K)).tsum_eq]
    simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

theorem runWord_bijective {S K : Type*} (U : K → S → S)
    (hU : ∀ k, Function.Bijective (U k)) (n : ℕ) (w : Fin n → K) :
    Function.Bijective (runWord U w) := by
  induction n with
  | zero => exact Function.bijective_id
  | succ n ih =>
      exact (ih (fun i : Fin n => w i.succ)).comp (hU (w 0))

theorem cubeUpdate_bijective {I : Type*} [Fintype I] [DecidableEq I]
    (V : Finset Site) (edge : I → V × V) (c : I → ℕ) :
    Function.Bijective (cubeUpdate V edge c) := by
  unfold cubeUpdate sparseUpdate
  split
  · exact (FiniteGenerator.colorSwap _ _).bijective
  · exact Function.bijective_id

theorem grid_uniform {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (V : Finset Site)
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (n : ℕ) (h : ℝ) (hh : 0 < h) (ξ : V → Bool) :
    μ {ω | gridApprox V P edge h n ω = ξ} = (1 / 2 : ℝ≥0∞) ^ V.card := by
  apply uniform_random_bijection (fun ω => restrictColor V (P.initial ω))
    (fun ω => gridWord (P.clocks ω) (siteEdges V edge) h n)
    (Measurable.of_eval (fun v => (measurable_pi_apply (v : Site)).comp P.measurable_initial))
    (measurable_gridWord V P edge h n)
    (runWord (cubeUpdate V edge)) (runWord_bijective _ (cubeUpdate_bijective V edge) n)
    _ (fun w => ∏ j, productMass (fun i => rate (edgePair V edge i) * h) (w j))
  · rw [tsum_fin_product]
    simp [productMass_sum _ (fun i => mul_nonneg (hr i) hh.le)]
  · exact grid_joint_count_law V P edge hinj n h hh

theorem projected_uniform {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (V : Finset Site)
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (t : ℝ) (ht : 0 < t) (ξ : V → Bool) :
    μ {ω | projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
      edge (P.initial ω) t = ξ} = (1 / 2 : ℝ≥0∞) ^ V.card := by
  apply event_probability_eq_of_approximation (fun _ => ξ)
    (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t)
    (fun n => gridApprox V P edge (t/n) n) (fun _ η => η = ξ)
  · apply tendsto_atTop_of_eventually_const (i₀ := 1)
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact grid_uniform V P edge hinj hr n (t/n) (div_pos ht hn') ξ
  · simpa only [ne_comm] using tendsto_projected_discrepancy V P edge hinj hr t ht

theorem projected_preserves_event {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (V : Finset Site)
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (t : ℝ) (ht : 0 < t) (E : (V → Bool) → Prop) :
    μ {ω | E (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
      edge (P.initial ω) t)} = μ {ω | E (restrictColor V (P.initial ω))} := by
  let X := fun ω => restrictColor V (P.initial ω)
  let Y := fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t
  have hX : Measurable X := Measurable.of_eval (fun v =>
    (measurable_pi_apply (v : Site)).comp P.measurable_initial)
  have hY := aemeasurable_projectedTrajectory V P edge hinj hr t ht
  have hm : μ.map Y = μ.map X := by
    apply Measure.ext_of_singleton
    intro ξ
    rw [Measure.map_apply_of_aemeasurable hY (measurableSet_singleton ξ),
      Measure.map_apply hX (measurableSet_singleton ξ)]
    change μ {ω | Y ω = ξ} = μ {ω | X ω = ξ}
    rw [projected_uniform V P edge hinj hr t ht ξ]
    symm
    simp only [X, restrictColor_eq_iff]
    exact P.independent_law.fair_initial V (extendColor V ξ)
  change μ (Y ⁻¹' {η | E η}) = μ (X ⁻¹' {η | E η})
  rw [← Measure.map_apply_of_aemeasurable hY (MeasurableSet.of_discrete),
    ← Measure.map_apply hX (MeasurableSet.of_discrete), hm]

theorem truncated_preserves_local_event {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : Finset (Sym2 Site)) (A : Finset Site)
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ)) (t : ℝ) :
    μ {ω | E (P.truncatedTrajectories F ω t)} = μ {ω | E (P.initial ω)} := by
  by_cases ht : 0 < t
  · let V := FiniteEdgeEnumeration.vertices F ∪ A
    have hv : FiniteEdgeEnumeration.vertices F ⊆ V := Finset.subset_union_left
    have ha : A ⊆ V := Finset.subset_union_right
    have H := projected_preserves_event V P (FiniteEdgeEnumeration.enumerate F V hv)
      (FiniteEdgeEnumeration.enumerate_injective F V hv) (fun _ => hr _) t ht
      (fun ξ => E (extendColor V ξ))
    change μ {ω | E (extendColor V (restrictColor V
      (P.truncatedTrajectories (retainedEdges V (FiniteEdgeEnumeration.enumerate F V hv)) ω t)))} =
        μ {ω | E (extendColor V (restrictColor V (P.initial ω)))} at H
    rw [FiniteEdgeEnumeration.enumerate_retainedEdges] at H
    simpa only [← FiniteMatchingComparison.frame_event_iff A V ha E hlocal] using H
  · simp only [P.truncated_nonpos F _ (le_of_not_gt ht)]

theorem preserves_local_event {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n) (A : Finset Site)
    (E : Configuration → Prop) (hE : MeasurableSet {η | E η})
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ)) (t : ℝ) :
    μ {ω | E (P.trajectories ω t)} = μ {ω | E (P.initial ω)} := by
  let : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  let test : Configuration → Configuration → ℝ≥0∞ := fun _ η => if E η then 1 else 0
  have hm (n : ℕ) : NullMeasurableSet {ω | E (P.truncatedTrajectories (F n) ω t)} μ :=
    (P.aemeasurable_truncated hr (F n) t).nullMeasurableSet_preimage hE
  have hmfull : NullMeasurableSet {ω | E (P.trajectories ω t)} μ :=
    (P.aemeasurable_trajectories_of_exhaustion hr F hmono hex t).nullMeasurableSet_preimage hE
  have htest : ∀ n, AEMeasurable
      (fun ω => test (P.initial ω) (P.truncatedTrajectories (F n) ω t)) μ := by
    intro n
    have hi := (aemeasurable_const (b := (1 : ℝ≥0∞))).indicator₀ (hm n)
    convert hi using 1
    funext ω
    simp [test, Set.indicator_apply]
  have hlim : Tendsto
      (fun n => ∫⁻ ω, test (P.initial ω) (P.truncatedTrajectories (F n) ω t) ∂μ)
      atTop (𝓝 (∫⁻ ω, test (P.initial ω) (P.trajectories ω t) ∂μ)) := by
    apply tendsto_lintegral_of_dominated_convergence' (fun _ => 1) htest
    · intro n
      exact ae_of_all μ (fun ω => by dsimp [test]; split <;> simp)
    · simp
    · apply ae_of_all μ
      intro ω
      have hl : ∀ initial η ξ, (∀ x ∈ A, η x = ξ x) → test initial η = test initial ξ := by
        intro initial η ξ heq
        simp only [test, hlocal η ξ heq]
      obtain ⟨N, hN⟩ := P.eventually_truncated_two_time_test_eq F hmono hex t A test hl ω
      exact tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => hN n hn)
  have hleft (n : ℕ) :
      (∫⁻ ω, test (P.initial ω) (P.truncatedTrajectories (F n) ω t) ∂μ) =
        μ {ω | E (P.initial ω)} := by
    have hi : (∫⁻ ω, test (P.initial ω) (P.truncatedTrajectories (F n) ω t) ∂μ) =
        μ {ω | E (P.truncatedTrajectories (F n) ω t)} := by
      simpa only [Set.indicator, Set.mem_ofPred_eq, test, one_mul] using
        lintegral_indicator_const₀ (hm n) (1 : ℝ≥0∞)
    exact hi.trans (truncated_preserves_local_event P hr (F n) A E hlocal t)
  have hright : (∫⁻ ω, test (P.initial ω) (P.trajectories ω t) ∂μ) =
      μ {ω | E (P.trajectories ω t)} := by
    simpa only [Set.indicator, Set.mem_ofPred_eq, test, one_mul] using
      lintegral_indicator_const₀ hmfull (1 : ℝ≥0∞)
  simp only [hleft, hright] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem oneArm_marginal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (v : Site) (R : ℕ) (hv : v ∈ latticeBox R) (t : ℝ) :
    μ {ω | OneArm (P.trajectories ω t) v R} = μ {ω | OneArm (P.initial ω) v R} := by
  apply preserves_local_event P hr F hmono hex (latticeBox (R+1))
    (fun η => OneArm η v R) (measurableSet_oneArm v R) ?_ t
  intro η ξ heq
  exact oneArm_congr_of_eqOn_box hv (fun x hx => heq x hx)

end ExceptionalTimes.FiniteClockMarginal

#print axioms ExceptionalTimes.FiniteClockMarginal.grid_uniform
#print axioms ExceptionalTimes.FiniteClockMarginal.projected_uniform
#print axioms ExceptionalTimes.FiniteClockMarginal.truncated_preserves_local_event
#print axioms ExceptionalTimes.FiniteClockMarginal.oneArm_marginal
