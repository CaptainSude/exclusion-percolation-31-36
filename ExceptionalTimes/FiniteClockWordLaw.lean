import ExceptionalTimes.FiniteClockSlicePath

open MeasureTheory
open scoped BigOperators ENNReal Classical Matrix

namespace ExceptionalTimes.FiniteClockWordLaw

variable {S K : Type*}

noncomputable def runWord (U : K → S → S) : {n : ℕ} → (Fin n → K) → S → S
  | 0, _, x => x
  | n + 1, w, x => runWord U (fun i : Fin n => w i.succ) (U (w 0) x)

theorem runWord_snoc (U : K → S → S) {n : ℕ} (w : Fin n → K) (k : K) (x : S) :
    runWord U (Fin.snoc w k) x = U k (runWord U w x) := by
  induction n generalizing x with
  | zero => simp [runWord, Fin.snoc]
  | succ n ih =>
    have hw : w = Fin.cons (w 0) (fun i : Fin n => w i.succ) := by ext i; exact (Fin.cons_self_tail w).symm ▸ rfl
    conv_lhs => rw [hw, ← Fin.cons_snoc_eq_snoc_cons]
    simp only [runWord, Fin.cons_zero, Fin.cons_succ]
    exact ih _ _

noncomputable def transition (p : K → ℝ≥0∞) (U : K → S → S) : Matrix S S ℝ≥0∞ :=
  fun x y => ∑' k, if U k x = y then p k else 0

theorem transition_action [Fintype S] (p : K → ℝ≥0∞) (U : K → S → S)
    (x : S) (g : S → ℝ≥0∞) :
    (∑' k, p k * g (U k x)) = ∑ y, transition p U x y * g y := by
  classical
  simp only [transition, ← ENNReal.tsum_mul_right]
  rw [← tsum_fintype (L := SummationFilter.unconditional S), ENNReal.tsum_comm]
  apply tsum_congr
  intro k
  simp [tsum_fintype]

theorem word_transition [Fintype S] [DecidableEq S]
    (p : K → ℝ≥0∞) (U : K → S → S) (n : ℕ) (x y : S) :
    (∑' w : Fin n → K, if runWord U w x = y then ∏ j, p (w j) else 0) =
      (transition p U ^ n) x y := by
  classical
  induction n generalizing x with
  | zero => simp [runWord, Matrix.one_apply]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => K)).tsum_eq, ENNReal.tsum_prod']
    simp only [Fin.consEquiv_apply, runWord, Fin.cons_zero, Fin.cons_succ,
      Fin.prod_univ_succ]
    calc
      (∑' k, ∑' w : Fin n → K,
          if runWord U w (U k x) = y then p k * ∏ j, p (w j) else 0) =
          ∑' k, p k * (transition p U ^ n) (U k x) y := by
        apply tsum_congr
        intro k
        rw [← ih, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro w
        split_ifs <;> simp
      _ = ∑ z, transition p U x z * (transition p U ^ n) z y :=
        transition_action p U x (fun z => (transition p U ^ n) z y)
      _ = (transition p U ^ (n + 1)) x y := by
        rw [pow_succ', Matrix.mul_apply]

theorem joint_word_law {Ξ : Type*} [MeasurableSpace Ξ]
    [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
    {μ : Measure Ξ} (n : ℕ) (X : Ξ → S) (W : Ξ → Fin n → K)
    (hX : Measurable X) (hW : Measurable W) (a : S → ℝ≥0∞)
    (p : K → ℝ≥0∞) (U : K → S → S)
    (hlaw : ∀ x w, μ {ω | X ω = x ∧ W ω = w} = a x * ∏ j, p (w j))
    (x y : S) :
    μ {ω | X ω = x ∧ runWord U (W ω) (X ω) = y} =
      a x * (transition p U ^ n) x y := by
  rw [PoissonDimerLaw.joint_update_eq_tsum hX hW (runWord U), ← word_transition,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro w
  rw [hlaw]
  split_ifs <;> simp

#print axioms joint_word_law

open FiniteClockSlices

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def sparseUpdate (σ : I → S → S) (c : I → ℕ) (x : S) : S :=
  if hc : ∃ i, c = Pi.single i 1 then σ hc.choose x else x

theorem sparseUpdate_single (σ : I → S → S) (i : I) (x : S) :
    sparseUpdate σ (Pi.single i 1) x = σ i x := by
  have hex : ∃ j, (Pi.single i 1 : I → ℕ) = Pi.single j 1 := ⟨i, rfl⟩
  have hi : hex.choose = i := (single_injective hex.choose_spec).symm
  simp only [sparseUpdate, dite_eq_left hex, hi]

theorem sparse_transition (p : (I → ℕ) → ℝ≥0∞) (σ : I → S → S)
    (hp : ∑' c, p c = 1) (x y : S) :
    transition p (sparseUpdate σ) x y =
      (if x = y then 1 - ∑ i, p (Pi.single i 1) else 0) +
        ∑ i, if σ i x = y then p (Pi.single i 1) else 0 := by
  classical
  let F : Finset (I → ℕ) := Finset.univ.image (fun i => Pi.single i 1)
  have hmem (c : I → ℕ) : c ∈ F ↔ ∃ i, c = Pi.single i 1 := by
    simp [F, eq_comm]
  have hcomp : (∑' c : ↥(F : Set (I → ℕ))ᶜ, p c) = 1 - ∑ i, p (Pi.single i 1) := by
    have he := ENNReal.sum_add_tsum_compl F p
    rw [hp, Finset.sum_image (fun i _ j _ hij => single_injective hij)] at he
    exact ENNReal.eq_sub_of_add_eq' (by simp) ((add_comm _ _).trans he)
  unfold transition
  rw [← ENNReal.sum_add_tsum_compl F]
  have hfirst : (∑ c ∈ F, if sparseUpdate σ c x = y then p c else 0) =
      ∑ i, if σ i x = y then p (Pi.single i 1) else 0 := by
    rw [Finset.sum_image (fun i _ j _ hij => single_injective hij)]
    simp only [sparseUpdate_single]
  have hlast : (∑' c : ↥(F : Set (I → ℕ))ᶜ,
      if sparseUpdate σ c x = y then p c else 0) =
      if x = y then 1 - ∑ i, p (Pi.single i 1) else 0 := by
    have hU (c : ↥(F : Set (I → ℕ))ᶜ) : sparseUpdate σ c x = x := by
      apply dite_eq_right
      exact fun h => c.property ((hmem c).mpr h)
    simp only [hU]
    split_ifs with h
    · exact hcomp
    · simp
  rw [hfirst, hlast, add_comm]

theorem poissonMass_sum (r : ℝ) (hr : 0 ≤ r) : (∑' n, poissonMass r n) = 1 := by
  have hs := PoissonDimerLaw.hasSum_poissonReal r
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← hs.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (PoissonDimerLaw.poissonReal_nonneg hr) hs.summable]
  rfl

omit [DecidableEq I] in
theorem productMass_sum (mean : I → ℝ) (hm : ∀ i, 0 ≤ mean i) :
    (∑' c, productMass mean c) = 1 := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E : (Fin (Fintype.card I) → ℕ) ≃ (I → ℕ) :=
    Equiv.arrowCongr e (Equiv.refl ℕ)
  rw [← E.tsum_eq]
  have he (w : Fin (Fintype.card I) → ℕ) : productMass mean (E w) =
      ∏ j, poissonMass (mean (e j)) (w j) := by
    unfold productMass
    simpa [E] using (e.prod_comp (fun i => poissonMass (mean i) ((E w) i))).symm
  simp only [he]
  rw [PoissonDimerLaw.tsum_fin_prod]
  simp [poissonMass_sum _ (hm _)]

theorem poisson_sparse_transition (mean : I → ℝ) (hm : ∀ i, 0 ≤ mean i)
    (σ : I → S → S) (x y : S) :
    transition (productMass mean) (sparseUpdate σ) x y =
      (if x = y then ENNReal.ofReal (1 - Real.exp (-(∑ i, mean i)) * ∑ i, mean i)
        else 0) +
      ∑ i, if σ i x = y then ENNReal.ofReal (Real.exp (-(∑ j, mean j)) * mean i)
        else 0 := by
  rw [sparse_transition _ _ (productMass_sum mean hm)]
  simp only [productMass_single mean hm]
  congr 2
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (Real.exp_pos _).le (hm i)), ← Finset.mul_sum,
    ENNReal.ofReal_sub _ (mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun i _ => hm i)))]
  simp

#print axioms poisson_sparse_transition

noncomputable def realStep (mean : I → ℝ) (σ : I → S → S) : Matrix S S ℝ :=
  fun x y => (if x = y then 1 - Real.exp (-(∑ i, mean i)) * ∑ i, mean i else 0) +
    ∑ i, if σ i x = y then Real.exp (-(∑ j, mean j)) * mean i else 0

theorem exp_mul_self_le_one (a : ℝ) : Real.exp (-a) * a ≤ 1 := by
  calc
    Real.exp (-a) * a ≤ Real.exp (-a) * Real.exp a :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

omit [DecidableEq I] in
theorem realStep_nonneg (mean : I → ℝ) (hm : ∀ i, 0 ≤ mean i)
    (σ : I → S → S) (x y : S) : 0 ≤ realStep mean σ x y := by
  apply add_nonneg
  · split_ifs
    · exact sub_nonneg.mpr (exp_mul_self_le_one _)
    · exact le_refl 0
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (hm i)
    · exact le_refl 0

theorem poisson_transition_eq_ofReal (mean : I → ℝ) (hm : ∀ i, 0 ≤ mean i)
    (σ : I → S → S) (x y : S) :
    transition (productMass mean) (sparseUpdate σ) x y = ENNReal.ofReal (realStep mean σ x y) := by
  rw [poisson_sparse_transition mean hm]
  unfold realStep
  rw [ENNReal.ofReal_add (by split_ifs; exact sub_nonneg.mpr (exp_mul_self_le_one _); rfl)
    (Finset.sum_nonneg (fun i _ => by split_ifs; exact mul_nonneg (Real.exp_pos _).le (hm i); rfl)),
    ENNReal.ofReal_sum_of_nonneg
      (fun i _ => by split_ifs; exact mul_nonneg (Real.exp_pos _).le (hm i); rfl)]
  congr 1
  · split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

omit [DecidableEq I] in
theorem realStep_eq_euler [Fintype S] [DecidableEq S]
    (rate : I → ℝ) (σ : I → Equiv.Perm S) (h : ℝ) :
    realStep (fun i => rate i * h) (fun i => σ i) =
      1 - (h * Real.exp (-(∑ i, rate i) * h)) • FiniteGenerator.generatorMatrix σ rate := by
  ext x y
  simp only [realStep, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, FiniteGenerator.generatorMatrix, FiniteGenerator.jumpMatrix,
    ← Finset.sum_mul, neg_mul]
  have hs : (∑ i, if σ i x = y then Real.exp (-((∑ j, rate j) * h)) * (rate i * h) else 0) =
      (h * Real.exp (-((∑ j, rate j) * h))) * ∑ i, if σ i x = y then rate i else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [hs]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  by_cases hxy : x = y <;> simp only [hxy, ite_true, ite_false, Finset.sum_const_zero] <;> ring

theorem matrix_power_nonneg [Fintype S] [DecidableEq S] (M : Matrix S S ℝ)
    (hM : ∀ x y, 0 ≤ M x y) (n : ℕ) (x y : S) : 0 ≤ (M ^ n) x y := by
  induction n generalizing x y with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (hM x z) (ih z y))

theorem ofReal_matrix_power [Fintype S] [DecidableEq S] (M : Matrix S S ℝ)
    (hM : ∀ x y, 0 ≤ M x y) (n : ℕ) :
    (M.map ENNReal.ofReal) ^ n = (M ^ n).map ENNReal.ofReal := by
  induction n with
  | zero => ext x y; simp only [pow_zero, Matrix.map_apply, Matrix.one_apply]; split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ', pow_succ' M, ih]
    ext x y
    simp only [Matrix.mul_apply, Matrix.map_apply]
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun z _ => mul_nonneg (hM x z) (matrix_power_nonneg M hM n z y))]
    apply Finset.sum_congr rfl
    intro z _
    exact (ENNReal.ofReal_mul (hM x z)).symm

theorem poisson_transition_power [Fintype S] [DecidableEq S]
    (mean : I → ℝ) (hm : ∀ i, 0 ≤ mean i) (σ : I → S → S) (n : ℕ) :
    transition (productMass mean) (sparseUpdate σ) ^ n =
      (realStep mean σ ^ n).map ENNReal.ofReal := by
  have he : transition (productMass mean) (sparseUpdate σ) = (realStep mean σ).map ENNReal.ofReal := by
    ext x y
    exact poisson_transition_eq_ofReal mean hm σ x y
  rw [he, ofReal_matrix_power _ (realStep_nonneg mean hm σ)]

#print axioms poisson_transition_power

end ExceptionalTimes.FiniteClockWordLaw
