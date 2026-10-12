import ExceptionalTimes.FiniteClockWordLaw
import ExceptionalTimes.EulerSemigroup
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators ENNReal Classical Matrix

namespace ExceptionalTimes.FiniteClockGridLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FiniteClockBridge FiniteClockSlicePath FiniteClockSlices FiniteClockWordLaw FiniteGenerator

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def gridWord (C : ClockField) (edge : I → Site × Site) (h : ℝ) (n : ℕ) :
    Fin n → I → ℕ := fun j => sliceCounts C edge ((j.val : ℝ) * h) (((j.val : ℝ) + 1) * h)

omit [Fintype I] [DecidableEq I] in
theorem gridWord_snoc (C : ClockField) (edge : I → Site × Site) (h : ℝ) (n : ℕ) :
    gridWord C edge h (n + 1) = Fin.snoc (gridWord C edge h n)
      (sliceCounts C edge ((n : ℝ) * h) (((n : ℝ) + 1) * h)) := by
  ext j i
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [gridWord]
  · simp [gridWord]

theorem runGrid_eq_runWord (C : ClockField) (edge : I → Site × Site) (h : ℝ)
    (η : Configuration) (n : ℕ) :
    runGrid C edge h η n = runWord (countUpdate edge) (gridWord C edge h n) η := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runGrid, gridWord_snoc, runWord_snoc, ih]

variable (V : Finset Site)

noncomputable def cubeUpdate (edge : I → V × V) : (I → ℕ) → (V → Bool) → (V → Bool) :=
  sparseUpdate (fun i => colorSwap (edge i).1 (edge i).2)

theorem restrictColor_countUpdate (edge : I → V × V) (c : I → ℕ) (η : Configuration) :
    restrictColor V (countUpdate (siteEdges V edge) c η) = cubeUpdate V edge c (restrictColor V η) := by
  unfold countUpdate cubeUpdate sparseUpdate
  split_ifs with hc
  · exact restrictColor_swap V _ _ η
  · rfl

theorem restrictColor_runWord (edge : I → V × V) (n : ℕ) (w : Fin n → I → ℕ)
    (η : Configuration) :
    restrictColor V (runWord (countUpdate (siteEdges V edge)) w η) =
      runWord (cubeUpdate V edge) w (restrictColor V η) := by
  induction n generalizing η with
  | zero => rfl
  | succ n ih =>
    simp only [runWord]
    rw [ih, restrictColor_countUpdate]

theorem projectedTrajectory_eq_grid_of_good (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (edge : I → V × V) (η : Configuration) (h : ℝ)
    (hh : 0 ≤ h) (n : ℕ) (hgood : ∀ j : Fin n,
      GoodCounts (gridWord C (siteEdges V edge) h n j)) :
    projectedTrajectory V C hc edge η ((n : ℝ) * h) =
      runWord (cubeUpdate V edge) (gridWord C (siteEdges V edge) h n) (restrictColor V η) := by
  let F := retainedEdges V edge
  have hs : ∀ u v t, (C.restrictEdges F).Rings u v t → ∃ i,
      s(u, v) = pairIndex (siteEdges V edge) i := by
    intro u v t hr
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((ClockField.restrictEdges_rings C F u v t).mp hr).1
    exact ⟨i, hi.symm⟩
  have hcounts (a b : ℝ) : sliceCounts (C.restrictEdges F) (siteEdges V edge) a b =
      sliceCounts C (siteEdges V edge) a b := by
    funext i
    apply restricted_markCount_of_mem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hpath := trajectory_eq_runGrid_of_good (C.restrictEdges F)
    (restricted_finite_counts C hc F) (ht.restrictEdges F)
    (ClockField.restrictEdges_hasFiniteBackwardTraces hc F)
    (siteEdges V edge) hs η h hh n (fun j hj => by
      rw [hcounts]
      exact hgood ⟨j, hj⟩)
  unfold projectedTrajectory
  rw [hpath, runGrid_eq_runWord, restrictColor_runWord]
  congr 1
  ext j i
  exact congrFun (hcounts _ _) i

variable {Ξ : Type*} [MeasurableSpace Ξ]

omit [DecidableEq I] in
theorem grid_joint_count_law {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (n : ℕ) (h : ℝ) (hh : 0 < h)
    (η : V → Bool) (w : Fin n → I → ℕ) :
    μ {ω | restrictColor V (P.initial ω) = η ∧
      gridWord (P.clocks ω) (siteEdges V edge) h n = w} =
      (1 / 2 : ℝ≥0∞) ^ V.card * ∏ j, productMass (fun i => rate (edgePair V edge i) * h) (w j) := by
  have H := indexed_joint_count_law P.independent_law V η
    (gridTests (edgePair V edge) hinj n h hh) (fun ji => w ji.1 ji.2)
  have he : {ω | restrictColor V (P.initial ω) = η ∧
      gridWord (P.clocks ω) (siteEdges V edge) h n = w} =
      {ω | restrictColor V (P.initial ω) = η ∧
        (fun ji : Fin n × I => (P.clocks ω).markCount (edgePair V edge ji.2)
          ((ji.1.val : ℝ) * h) (((ji.1.val : ℝ) + 1) * h)) = (fun ji => w ji.1 ji.2)} := by
    ext ω
    simp [funext_iff, gridWord, sliceCounts, pairIndex, siteEdges, edgePair]
  rw [he]
  simp only [gridTests] at H
  rw [H]
  congr 1
  simp only [productMass, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  ring

omit [Fintype I] [DecidableEq I] in
theorem measurable_gridWord {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V) (h : ℝ) (n : ℕ) :
    Measurable (fun ω => gridWord (P.clocks ω) (siteEdges V edge) h n) :=
  Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => P.measurable_counts _ _ _))

theorem grid_joint_transition {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (n : ℕ) (h : ℝ) (hh : 0 < h) (η ξ : V → Bool) :
    μ {ω | restrictColor V (P.initial ω) = η ∧
      runWord (cubeUpdate V edge) (gridWord (P.clocks ω) (siteEdges V edge) h n)
        (restrictColor V (P.initial ω)) = ξ} =
      (1 / 2 : ℝ≥0∞) ^ V.card * ENNReal.ofReal
        ((realStep (fun i => rate (edgePair V edge i) * h)
          (fun i => colorSwap (edge i).1 (edge i).2) ^ n) η ξ) := by
  have hx : Measurable (fun ω => restrictColor V (P.initial ω)) :=
    Measurable.of_eval (fun v => (measurable_pi_apply (v : Site)).comp P.measurable_initial)
  rw [joint_word_law n _ _ hx (measurable_gridWord V P edge h n)
    (fun _ => (1 / 2 : ℝ≥0∞) ^ V.card) _ _ (grid_joint_count_law V P edge hinj n h hh)]
  rw [cubeUpdate, poisson_transition_power _ (fun i => mul_nonneg (hr i) hh.le)]
  rfl

#print axioms projectedTrajectory_eq_grid_of_good
#print axioms grid_joint_transition

noncomputable def gridApprox {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V) (h : ℝ) (n : ℕ)
    (ω : Ξ) : V → Bool :=
  runWord (cubeUpdate V edge) (gridWord (P.clocks ω) (siteEdges V edge) h n)
    (restrictColor V (P.initial ω))

theorem measurable_gridApprox {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V) (h : ℝ) (n : ℕ) :
    Measurable (gridApprox V P edge h n) := by
  have hx : Measurable (fun ω => restrictColor V (P.initial ω)) :=
    Measurable.of_eval (fun v => (measurable_pi_apply (v : Site)).comp P.measurable_initial)
  exact (Measurable.of_discrete (f := fun z : (Fin n → I → ℕ) × (V → Bool) =>
    runWord (cubeUpdate V edge) z.1 z.2)).comp ((measurable_gridWord V P edge h n).prodMk hx)

theorem projected_discrepancy_le {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (n : ℕ) (h : ℝ) (hh : 0 < h) :
    μ {ω | projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω)
        ((n : ℝ) * h) ≠ gridApprox V P edge h n ω} ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (((∑ i, rate (edgePair V edge i)) * h) ^ 2) := by
  apply le_trans (measure_mono (t := {ω | ∃ j : Fin n,
    ¬GoodCounts (gridWord (P.clocks ω) (siteEdges V edge) h n j)}) ?_)
  · exact graphical_grid_bad_probability_le P (edgePair V edge) hinj hr n h hh
  · intro ω hne
    by_contra hn
    have hn : ∀ j : Fin n, GoodCounts (gridWord (P.clocks ω) (siteEdges V edge) h n j) := by
      intro j
      by_contra hj
      exact hn ⟨j, hj⟩
    exact hne (projectedTrajectory_eq_grid_of_good V (P.clocks ω) (P.finiteEdgeCounts ω)
      (P.no_incident_ties ω) edge (P.initial ω) h hh.le n hn)

omit [Fintype I] [DecidableEq I] in
theorem grid_error_bound_limit (Λ t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ≥0∞) * ENNReal.ofReal ((Λ * (t / n)) ^ 2)) atTop (𝓝 0) := by
  have he (n : ℕ) : (n : ℝ≥0∞) * ENNReal.ofReal ((Λ * (t / n)) ^ 2) =
      ENNReal.ofReal ((Λ * t) ^ 2 / n) := by
    rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) by simp,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 1
    by_cases hn : n = 0
    · subst n; simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
  simp only [he]
  have H : Tendsto (fun n : ℕ => (Λ * t) ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp H

theorem tendsto_projected_discrepancy {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => μ {ω | projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
      edge (P.initial ω) t ≠ gridApprox V P edge (t / n) n ω}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (grid_error_bound_limit (∑ i, rate (edgePair V edge i)) t) (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have H := projected_discrepancy_le V P edge hinj hr n (t / n) (div_pos ht hn')
  rwa [mul_div_cancel₀ t hn'.ne'] at H

theorem aemeasurable_projectedTrajectory {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (t : ℝ) (ht : 0 < t) :
    AEMeasurable (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
      edge (P.initial ω) t) μ := by
  let : PseudoMetricSpace (V → Bool) := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (V → Bool)
  have H : TendstoInMeasure μ (fun n : ℕ => gridApprox V P edge (t / n) n) atTop
      (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
        edge (P.initial ω) t) := by
    intro ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_projected_discrepancy V P edge hinj hr t ht) (fun _ => zero_le)
    intro n
    apply measure_mono
    intro ω hω he
    change ε ≤ edist (gridApprox V P edge (t / n) n ω)
      (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t) at hω
    rw [he, edist_self] at hω
    exact (not_le_of_gt hε) hω
  exact H.aemeasurable (fun n : ℕ => (measurable_gridApprox V P edge (t / n) n).aemeasurable)

#print axioms aemeasurable_projectedTrajectory

omit [Fintype I] [DecidableEq I] in
theorem measure_event_le_of_discrepancy {μ : Measure Ξ} {S : Type*}
    (X Y Z : Ξ → S) (E : S → S → Prop) :
    μ {ω | E (X ω) (Y ω)} ≤ μ {ω | E (X ω) (Z ω)} + μ {ω | Y ω ≠ Z ω} := by
  apply le_trans (measure_mono (t := {ω | E (X ω) (Z ω)} ∪ {ω | Y ω ≠ Z ω}) ?_)
    (measure_union_le _ _)
  intro ω hω
  change E (X ω) (Y ω) at hω
  by_cases he : Y ω = Z ω
  · exact Or.inl (by change E (X ω) (Z ω); simpa only [← he] using hω)
  · exact Or.inr he

omit [Fintype I] [DecidableEq I] in
theorem event_probability_eq_of_approximation {μ : Measure Ξ} {S : Type*}
    (X Y : Ξ → S) (Z : ℕ → Ξ → S) (E : S → S → Prop) {p : ℝ≥0∞}
    (hp : Tendsto (fun n => μ {ω | E (X ω) (Z n ω)}) atTop (𝓝 p))
    (he : Tendsto (fun n => μ {ω | Y ω ≠ Z n ω}) atTop (𝓝 0)) :
    μ {ω | E (X ω) (Y ω)} = p := by
  apply le_antisymm
  · simpa only [add_zero] using ge_of_tendsto (hp.add he)
      (Eventually.of_forall (fun n => measure_event_le_of_discrepancy X Y (Z n) E))
  · have hle : ∀ n, μ {ω | E (X ω) (Z n ω)} ≤
        μ {ω | E (X ω) (Y ω)} + μ {ω | Y ω ≠ Z n ω} := by
      intro n
      simpa only [ne_comm] using measure_event_le_of_discrepancy X (Z n) Y E
    simpa only [add_zero] using le_of_tendsto_of_tendsto hp (tendsto_const_nhds.add he)
      (Eventually.of_forall hle)

omit [DecidableEq I] in
theorem complex_realStep (rate : I → ℝ) (σ : I → Equiv.Perm (V → Bool)) (h : ℝ) :
    (realStep (fun i => rate i * h) (fun i => σ i)).map Complex.ofReal =
      1 - (h * Real.exp (-(∑ i, rate i) * h)) • FiniteFractional.complexGenerator σ rate := by
  rw [realStep_eq_euler,
    Matrix.map_sub _ Complex.ofReal_sub,
    Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one,
    Matrix.map_smul _ _ (fun a => by simp [Complex.ofReal_mul, Complex.real_smul])]
  rfl

omit [DecidableEq I] in
theorem grid_realStep_limit (rate : I → ℝ) (hr : ∀ i, 0 ≤ rate i)
    (edge : I → V × V) (t : ℝ) (η ξ : V → Bool) :
    Tendsto (fun n : ℕ =>
      ((realStep (fun i => rate i * (t / n)) (fun i => colorSwap (edge i).1 (edge i).2) ^ n) η ξ))
      atTop (𝓝 ((NormedSpace.exp ((-t) • FiniteFractional.complexGenerator
        (fun i => colorSwap (edge i).1 (edge i).2) rate)) η ξ).re) := by
  let σ := fun i => colorSwap (edge i).1 (edge i).2
  have hA : (FiniteFractional.complexGenerator σ rate).IsHermitian :=
    (FiniteFractional.posSemidef_complexification
      (generatorMatrix_posSemidef σ (fun _ => colorSwap_involutive _ _) rate hr)).isHermitian
  have H := EulerSemigroup.poisson_matrix_euler_limit hA t (∑ i, rate i)
  have Hentry := ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp H) η)) ξ)
  have Hr := Complex.continuous_re.continuousAt.tendsto.comp Hentry
  convert Hr using 1
  funext n
  have he := Matrix.map_pow
    (realStep (fun i => rate i * (t / n)) (fun i => σ i)) Complex.ofRealHom n
  rw [show (⇑Complex.ofRealHom) = Complex.ofReal by rfl, complex_realStep] at he
  have hxy := congrFun (congrFun he η) ξ
  exact congrArg Complex.re hxy

theorem projected_joint_kernel {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (t : ℝ) (ht : 0 < t) (η ξ : V → Bool) :
    μ {ω | restrictColor V (P.initial ω) = η ∧
      projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t = ξ} =
      (1 / 2 : ℝ≥0∞) ^ V.card * ENNReal.ofReal
        (((NormedSpace.exp ((-t) • FiniteFractional.complexGenerator
          (fun i => colorSwap (edge i).1 (edge i).2) (fun i => rate (edgePair V edge i)))) η ξ).re) := by
  apply event_probability_eq_of_approximation
    (fun ω => restrictColor V (P.initial ω))
    (fun ω => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t)
    (fun n => gridApprox V P edge (t / n) n) (fun x y => x = η ∧ y = ξ)
    ?_ (tendsto_projected_discrepancy V P edge hinj hr t ht)
  have HL := (ENNReal.continuous_ofReal.tendsto _).comp
    (grid_realStep_limit V (fun i => rate (edgePair V edge i)) hr edge t η ξ)
  have HC := ENNReal.Tendsto.const_mul (a := (1 / 2 : ℝ≥0∞) ^ V.card) HL (Or.inr (by finiteness))
  apply HC.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact (grid_joint_transition V P edge hinj hr n (t / n) (div_pos ht hn') η ξ).symm

#print axioms projected_joint_kernel

omit [DecidableEq I] in
theorem swap_exp_entry_nonneg (rate : I → ℝ) (hr : ∀ i, 0 ≤ rate i)
    (edge : I → V × V) (t : ℝ) (ht : 0 ≤ t) (η ξ : V → Bool) :
    0 ≤ ((NormedSpace.exp ((-t) • FiniteFractional.complexGenerator
      (fun i => colorSwap (edge i).1 (edge i).2) rate)) η ξ).re := by
  apply ge_of_tendsto (grid_realStep_limit V rate hr edge t η ξ)
  exact Eventually.of_forall (fun n => matrix_power_nonneg _
    (realStep_nonneg _ (fun i => mul_nonneg (hr i) (div_nonneg ht (Nat.cast_nonneg n))) _) n η ξ)

omit [Fintype I] [DecidableEq I] in
theorem cube_uniform_mass :
    (1 / 2 : ℝ≥0∞) ^ V.card = ENNReal.ofReal ((Fintype.card (V → Bool) : ℝ)⁻¹) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.ofReal_inv_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) V.card)]
  norm_num [ENNReal.ofReal_pow, ← ENNReal.inv_pow]

theorem projected_paired_correlation {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (t : ℝ) (ht : 0 < t) (E : (V → Bool) → Prop) :
    μ {ω | E (restrictColor V (P.initial ω)) ∧
      E (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t)} =
      ENNReal.ofReal (FiniteSpectralEnergy.correlation
        (FiniteFractional.complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
          (fun i => rate (edgePair V edge i))) (FiniteClockLaw.indicatorVector E) t) := by
  have hx : Measurable (fun ω => restrictColor V (P.initial ω)) :=
    Measurable.of_eval (fun v => (measurable_pi_apply (v : Site)).comp P.measurable_initial)
  apply FiniteClockLaw.paired_event_eq_quadraticForm hx.aemeasurable
    (aemeasurable_projectedTrajectory V P edge hinj hr t ht)
    _ (swap_exp_entry_nonneg V _ hr edge t ht.le) ?_ E
  intro η ξ
  rw [projected_joint_kernel V P edge hinj hr t ht, cube_uniform_mass,
    ← ENNReal.ofReal_mul (by positivity)]

#print axioms projected_paired_correlation

end ExceptionalTimes.FiniteClockGridLaw
