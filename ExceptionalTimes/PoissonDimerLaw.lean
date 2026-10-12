import ExceptionalTimes.FiniteClockBridge
import ExceptionalTimes.ManyDimerLaw

/-!
# The half-rate Poisson swap law is the canonical dimer law

This module proves the parity calculation from the exponential series.
Its clock rates and elapsed times are literal: a rate-1/2 exchange clock
has mean t/2, and its resulting refresh probability is 1-exp(-t).
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ExceptionalTimes.PoissonDimerLaw

set_option backward.isDefEq.respectTransparency false

open DimerLaw

noncomputable def poissonReal (r : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-r) * r ^ n / (n.factorial : ℝ)

theorem poissonReal_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ poissonReal r n := by unfold poissonReal; positivity

theorem hasSum_poissonReal (r : ℝ) : HasSum (poissonReal r) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp r).mul_left (Real.exp (-r)) using 1
  · funext n
    simp [poissonReal, mul_div_assoc]
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    simp

theorem hasSum_signed_poissonReal (r : ℝ) :
    HasSum (fun n => Real.exp (-r) * (-r) ^ n / (n.factorial : ℝ))
      (Real.exp (-2 * r)) := by
  convert (NormedSpace.expSeries_div_hasSum_exp (-r)).mul_left (Real.exp (-r)) using 1
  · funext n
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

theorem hasSum_even_poissonReal (r : ℝ) :
    HasSum (fun n => if Even n then poissonReal r n else 0)
      ((1 + Real.exp (-2 * r)) / 2) := by
  convert ((hasSum_poissonReal r).add (hasSum_signed_poissonReal r)).div_const 2 using 1
  funext n
  rcases Nat.even_or_odd n with he | ho
  · simp [he, poissonReal, he.neg_pow]
  · simp [Nat.not_even_iff_odd.mpr ho, poissonReal, ho.neg_pow]
    ring

theorem hasSum_odd_poissonReal (r : ℝ) :
    HasSum (fun n => if Even n then 0 else poissonReal r n)
      ((1 - Real.exp (-2 * r)) / 2) := by
  convert ((hasSum_poissonReal r).sub (hasSum_signed_poissonReal r)).div_const 2 using 1
  funext n
  rcases Nat.even_or_odd n with he | ho
  · simp [he, poissonReal, he.neg_pow]
  · simp [Nat.not_even_iff_odd.mpr ho, poissonReal, ho.neg_pow]
    ring

/-- Exactly n successive exchanges of the same dimer. -/
def afterCount (n : ℕ) (ω : Color) : Color :=
  if Even n then ω else swapped ω

theorem hasSum_swap_transition (r : ℝ) (ω η : Color) :
    HasSum (fun n => if afterCount n ω = η then poissonReal r n else 0)
      ((if ω = η then (1 + Real.exp (-2 * r)) / 2 else 0) +
        (if swapped ω = η then (1 - Real.exp (-2 * r)) / 2 else 0)) := by
  by_cases hω : ω = η <;> by_cases hs : swapped ω = η
  · convert hasSum_poissonReal r using 1
    · funext n
      simp only [afterCount]
      split_ifs <;> simp_all
    · simp only [ite_eq_left hω, ite_eq_left hs]
      ring
  · convert hasSum_even_poissonReal r using 1
    · funext n
      simp only [afterCount]
      split_ifs <;> simp_all
    · simp only [ite_eq_left hω, ite_eq_right hs, add_zero]
  · convert hasSum_odd_poissonReal r using 1
    · funext n
      simp only [afterCount]
      split_ifs <;> simp_all
    · simp only [ite_eq_right hω, ite_eq_left hs, zero_add]
  · convert (hasSum_zero (β := ℕ) (α := ℝ)) using 1
    · funext n
      simp only [afterCount]
      split_ifs <;> simp_all
    · simp only [ite_eq_right hω, ite_eq_right hs, add_zero]

/-- This is the exact stationary two-time dimer weight already used by
the finite conditional-replica and Harris arguments. -/
theorem hasSum_half_rate_twoTimeWeight (t : ℝ) (ω η : Color) :
    HasSum (fun n => (1 / 4 : ℝ) *
      (if afterCount n ω = η then poissonReal (t / 2) n else 0))
      (twoTimeWeight (refreshProbability t) ω η) := by
  convert (hasSum_swap_transition (t / 2) ω η).mul_left (1 / 4 : ℝ) using 1
  unfold twoTimeWeight refreshProbability
  rw [haarTransition_identity_swap]
  have ht : -2 * (t / 2) = -t := by ring
  rw [ht]
  split_ifs <;> ring

theorem half_rate_twoTimeWeight (t : ℝ) (ht : 0 ≤ t) (ω η : Color) :
    (∑' n, (1 / 4 : ℝ≥0∞) *
      (if afterCount n ω = η then poissonMass (t / 2) n else 0)) =
      ENNReal.ofReal (twoTimeWeight (refreshProbability t) ω η) := by
  have h := hasSum_half_rate_twoTimeWeight t ω η
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro n
    by_cases hn : afterCount n ω = η
    · simp [hn, poissonMass, poissonReal, ENNReal.ofReal_mul]
    · simp [hn]
  · intro n
    apply mul_nonneg (by norm_num)
    split_ifs
    · exact poissonReal_nonneg (by linarith) n
    · exact le_refl 0
  · exact h.summable

/-- A deterministic update from count data is measured by the disjoint
count fibers. This is valid for any countable count space. -/
theorem joint_update_eq_tsum {Ξ S K : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace K] [MeasurableSingletonClass K] [Countable K]
    {μ : Measure Ξ} {X : Ξ → S} {N : Ξ → K}
    (hX : Measurable X) (hN : Measurable N) (U : K → S → S) (ω η : S) :
    μ {a | X a = ω ∧ U (N a) (X a) = η} =
      ∑' n, if U n ω = η then μ {a | X a = ω ∧ N a = n} else 0 := by
  let A : K → Set Ξ := fun n => {a | X a = ω ∧ N a = n ∧ U n ω = η}
  have hset : {a | X a = ω ∧ U (N a) (X a) = η} = ⋃ n, A n := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A]
    constructor
    · rintro ⟨hω, hη⟩
      exact ⟨N a, hω, rfl, hω ▸ hη⟩
    · rintro ⟨n, hω, hn, hη⟩
      exact ⟨hω, by simpa only [hω, hn] using hη⟩
  have hd : Pairwise (fun m n => Disjoint (A m) (A n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro a hm hn
    exact hmn (hm.2.1.symm.trans hn.2.1)
  have hm : ∀ n, MeasurableSet (A n) := by
    intro n
    by_cases h : U n ω = η
    · have he : A n = {a | X a = ω} ∩ {a | N a = n} := by
        ext a
        simp [A, h]
      rw [he]
      exact (hX (measurableSet_singleton ω)).inter (hN (measurableSet_singleton n))
    · have he : A n = ∅ := by ext a; simp [A, h]
      rw [he]
      exact MeasurableSet.empty
  rw [hset, measure_iUnion hd hm]
  apply tsum_congr
  intro n
  by_cases h : U n ω = η <;> simp [A, h]

/-- The parity computation applies to any actual initial-pair/count
random variables with their stated independent Poisson joint law. -/
theorem random_pair_twoTimeWeight {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {X : Ξ → Color} {N : Ξ → ℕ}
    (hX : Measurable X) (hN : Measurable N) (t : ℝ) (ht : 0 ≤ t)
    (hlaw : ∀ ω n, μ {a | X a = ω ∧ N a = n} =
      (1 / 4 : ℝ≥0∞) * poissonMass (t / 2) n) (ω η : Color) :
    μ {a | X a = ω ∧ afterCount (N a) (X a) = η} =
      ENNReal.ofReal (twoTimeWeight (refreshProbability t) ω η) := by
  rw [joint_update_eq_tsum hX hN afterCount, ← half_rate_twoTimeWeight t ht]
  apply tsum_congr
  intro n
  split_ifs <;> simp_all

/-- Nonnegative count series factor across a finite family. -/
theorem tsum_fin_prod (k : ℕ) (f : Fin k → ℕ → ℝ≥0∞) :
    (∑' n : Fin k → ℕ, ∏ b, f b (n b)) = ∏ b, ∑' n, f b n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).tsum_eq]
    simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

def afterCounts {B : Type*} (n : B → ℕ) (ω : B → Color) : B → Color :=
  fun b => afterCount (n b) (ω b)

/-- The exact product dimer law follows from the full finite joint
initial-color/Poisson-count law; no process or semigroup law is assumed. -/
theorem random_many_twoTimeWeight {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} (k : ℕ) {X : Ξ → Fin k → Color} {N : Ξ → Fin k → ℕ}
    (hX : Measurable X) (hN : Measurable N) (t : ℝ) (ht : 0 ≤ t)
    (hlaw : ∀ ω n, μ {a | X a = ω ∧ N a = n} =
      (1 / 4 : ℝ≥0∞) ^ k * ∏ b, poissonMass (t / 2) (n b))
    (ω η : Fin k → Color) :
    μ {a | X a = ω ∧ afterCounts (N a) (X a) = η} =
      ENNReal.ofReal (ManyDimerLaw.manyWeight (fun _ => refreshProbability t) ω η) := by
  classical
  rw [joint_update_eq_tsum hX hN afterCounts]
  have hterm (n : Fin k → ℕ) :
      (if afterCounts n ω = η then μ {a | X a = ω ∧ N a = n} else 0) =
        ∏ b, (1 / 4 : ℝ≥0∞) *
          (if afterCount (n b) (ω b) = η b then poissonMass (t / 2) (n b) else 0) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Fintype.prod_ite_zero]
    have he : afterCounts n ω = η ↔ ∀ b, afterCount (n b) (ω b) = η b :=
      funext_iff
    by_cases h : afterCounts n ω = η
    · rw [ite_eq_left h, ite_eq_left (he.mp h), hlaw]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h (he.mpr hh)), mul_zero]
  calc
    _ = ∑' n : Fin k → ℕ, ∏ b, (1 / 4 : ℝ≥0∞) *
        (if afterCount (n b) (ω b) = η b then poissonMass (t / 2) (n b) else 0) := by
      apply tsum_congr
      intro n
      by_cases h : afterCounts n ω = η
      · simpa only [ite_eq_left h] using hterm n
      · simpa only [ite_eq_right h] using hterm n
    _ = _ := by
      rw [tsum_fin_prod k (fun b m => (1 / 4 : ℝ≥0∞) *
        (if afterCount m (ω b) = η b then poissonMass (t / 2) m else 0))]
      simp_rw [half_rate_twoTimeWeight t ht]
      rw [ManyDimerLaw.manyWeight, ENNReal.ofReal_prod_of_nonneg]
      intro b _
      exact twoTimeWeight_nonneg (refreshProbability_nonneg ht) (refreshProbability_le_one t) _ _

#print axioms random_pair_twoTimeWeight
#print axioms random_many_twoTimeWeight

open FiniteClockBridge

def pairProjection (x y : Site) (η : Configuration) : Color := pair (η x) (η y)

theorem pairProjection_swap (x y : Site) (η : Configuration) :
    pairProjection x y (η ∘ Equiv.swap x y) = swapped (pairProjection x y η) := by
  simp [pairProjection, swapped, pair]

@[simp] theorem swapped_swapped (η : Color) : swapped (swapped η) = η := by
  unfold swapped
  simpa [pair] using pair_ext η

theorem afterCount_succ (n : ℕ) (η : Color) :
    afterCount (n + 1) η = swapped (afterCount n η) := by
  by_cases hn : Even n <;> simp [afterCount, Nat.even_add_one, hn]

theorem runColors_single_pair (x y : Site) (events : List (ℝ × Unit))
    (η : Configuration) :
    pairProjection x y (runColors (fun _ : Unit => (x, y)) events η) =
      afterCount events.length (pairProjection x y η) := by
  induction events with
  | nil => simp [runColors, afterCount]
  | cons event events ih =>
    rw [runColors, pairProjection_swap, ih, List.length_cons, afterCount_succ]

theorem sweep_single_length {C : ClockField} {x y : Site}
    (hc : C.FiniteEdgeCounts) {c : TimeCutoff} {events : List (ℝ × Unit)}
    (h : IsSweep C (fun _ : Unit => (x, y)) c events) :
    events.length = (C.marks s(x, y) ∩ {r | c.Allows r}).ncard := by
  induction h with
  | @nil c h =>
    have he : C.marks s(x, y) ∩ {r | c.Allows r} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact h x y r hr.1 hr.2
    simp [he]
  | @cons c t i events h tail ih =>
    have he : C.marks s(x, y) ∩ {r | c.Allows r} =
        insert t (C.marks s(x, y) ∩ {r | r < t}) := by
      ext r
      constructor
      · intro hr
        by_cases hrt : r = t
        · exact Set.mem_insert_iff.mpr (Or.inl hrt)
        · exact Set.mem_insert_iff.mpr (Or.inr
            ⟨hr.1, lt_of_le_of_ne (h.latest x y r hr.1 hr.2) hrt⟩)
      · rintro (hrt | hr)
        · subst r
          exact ⟨h.rings, h.allowed⟩
        · exact ⟨hr.1, TimeCutoff.allows_of_lt h.allowed hr.2⟩
    have hfin : (C.marks s(x, y) ∩ {r | r < t}).Finite :=
      (hc s(x, y) t).subset (fun r hr => ⟨hr.1, C.positive_time _ _ hr.1, hr.2.le⟩)
    rw [he, Set.ncard_insert_of_notMem (by simp) hfin, List.length_cons]
    exact congrArg (fun n => n + 1) ih

/-- All rings of a one-edge restriction can be ordered, independently of
simultaneous rings on disjoint edges in the original field. -/
theorem sweep_single_exists (C : ClockField) (hc : C.FiniteEdgeCounts)
    (x y : Site) (c : TimeCutoff) :
    ∃ events, IsSweep (C.restrictEdges {s(x, y)}) (fun _ : Unit => (x, y)) c events := by
  let D := C.restrictEdges {s(x, y)}
  have hr (u v : Site) (t : ℝ) (h : D.Rings u v t) : s(u, v) = s(x, y) := by
    exact Finset.mem_singleton.mp ((ClockField.restrictEdges_rings C {s(x, y)} u v t).mp h).1
  apply sweep_exists_of_finite_time_support D (fun _ : Unit => (x, y))
    (fun u v z w t h₁ h₂ => (hr u v t h₁).trans (hr z w t h₂).symm)
    (fun u v t h => ⟨(), hr u v t h⟩) (hc s(x, y) c.time).toFinset c
  intro u v t h ha
  have hm := ((ClockField.restrictEdges_rings C {s(x, y)} u v t).mp h).2
  change t ∈ C.marks s(u, v) at hm
  rw [hr u v t h] at hm
  exact (hc s(x, y) c.time).mem_toFinset.mpr
    ⟨hm, C.positive_time _ _ hm, TimeCutoff.allows_le_time ha⟩

/-- The actual backward-trace trajectory on one retained edge is exactly
the parity of that edge's count. -/
theorem trajectory_single_pair (C : ClockField) (hc : C.FiniteEdgeCounts)
    (hC : C.NoIncidentTies) (x y : Site) (η : Configuration) (t : ℝ) :
    pairProjection x y ((C.restrictEdges {s(x, y)}).trajectory
      (ClockField.restrictEdges_hasFiniteBackwardTraces hc _) η t) =
      afterCount (C.markCount s(x, y) 0 t) (pairProjection x y η) := by
  obtain ⟨events, hs⟩ := sweep_single_exists C hc x y (TimeCutoff.closedAt t)
  unfold ClockField.trajectory
  rw [hs.colorAt_eq_runColors (hC.restrictEdges _) _, runColors_single_pair]
  have hc' := restricted_finite_counts C hc {s(x, y)}
  rw [sweep_single_length hc' hs]
  congr 1
  unfold ClockField.markCount
  congr 1
  ext r
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, TimeCutoff.allows_at,
    ClockField.restrictEdges, Finset.mem_singleton, ite_true, Set.mem_Ioc]
  exact ⟨fun h => ⟨h.1, C.positive_time _ _ h.1, h.2⟩,
    fun h => ⟨h.1, h.2.2⟩⟩

theorem pairProjection_eq_iff (x y : Site) (η : Configuration) (ω : Color) :
    pairProjection x y η = ω ↔ η x = ω 0 ∧ η y = ω 1 := by
  rw [← pair_ext ω]
  exact pair_eq_pair _ _ _ _

def singleTest (e : Sym2 Site) (t : ℝ) (ht : 0 < t) : ClockTests 1 where
  edge _ := e
  start _ := 0
  finish _ := t
  start_nonneg _ := le_refl 0
  nonempty _ := ht
  disjoint i j hij _ := (hij (Subsingleton.elim i j)).elim

/-- The single dimer's joint initial-color/count law is a proved direct
instance of the model's cylinder law on the two actual lattice sites. -/
theorem initial_pair_count_law {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ} {initial : Ξ → Configuration}
    {clocks : Ξ → ClockField} (hlaw : IndependentPoissonInitial μ rate initial clocks)
    (x y : Site) (hxy : x ≠ y) (t : ℝ) (ht : 0 < t) (ω : Color) (n : ℕ) :
    μ {a | pairProjection x y (initial a) = ω ∧
      (clocks a).markCount s(x, y) 0 t = n} =
      (1 / 4 : ℝ≥0∞) * poissonMass (rate s(x, y) * t) n := by
  let η : Configuration := fun v => if v = x then ω 0 else ω 1
  have he : {a | pairProjection x y (initial a) = ω ∧
      (clocks a).markCount s(x, y) 0 t = n} =
      {a | (∀ v ∈ ({x, y} : Finset Site), initial a v = η v) ∧
        ∀ i : Fin 1, (clocks a).markCount ((singleTest s(x, y) t ht).edge i)
          ((singleTest s(x, y) t ht).start i) ((singleTest s(x, y) t ht).finish i) = n} := by
    ext a
    simp [pairProjection_eq_iff, η, Ne.symm hxy, singleTest]
  rw [he, hlaw {x, y} η 1 (singleTest s(x, y) t ht) (fun _ => n)]
  norm_num [singleTest, hxy]
  rw [← ENNReal.inv_pow]
  norm_num

theorem measurable_pairProjection {Ξ : Type*} [MeasurableSpace Ξ]
    {initial : Ξ → Configuration} (hi : Measurable initial) (x y : Site) :
    Measurable (fun a => pairProjection x y (initial a)) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · simpa [pairProjection, pair, Function.comp_def] using (measurable_pi_apply x).comp hi
  · simpa [pairProjection, pair, Function.comp_def] using (measurable_pi_apply y).comp hi

/-- Canonical dimer joint probabilities are now identified for the actual
same-clock restricted graphical trajectories, with no semigroup input. -/
theorem graphical_single_pair_twoTimeWeight {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (x y : Site) (hxy : x ≠ y)
    (hrate : rate s(x, y) = 1 / 2) (t : ℝ) (ht : 0 < t) (ω η : Color) :
    μ {a | pairProjection x y (P.initial a) = ω ∧
      pairProjection x y (((P.clocks a).restrictEdges {s(x, y)}).trajectory
        (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts a) _)
        (P.initial a) t) = η} =
      ENNReal.ofReal (twoTimeWeight (refreshProbability t) ω η) := by
  have hlaw : ∀ ξ n, μ {a | pairProjection x y (P.initial a) = ξ ∧
      (P.clocks a).markCount s(x, y) 0 t = n} =
      (1 / 4 : ℝ≥0∞) * poissonMass (t / 2) n := by
    intro ξ n
    have h := initial_pair_count_law P.independent_law x y hxy t ht ξ n
    rw [hrate] at h
    convert h using 2
    congr 1
    ring
  have h := random_pair_twoTimeWeight (measurable_pairProjection P.measurable_initial x y)
    (P.measurable_counts s(x, y) 0 t) t ht.le hlaw ω η
  convert h using 1
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [trajectory_single_pair (P.clocks a) (P.finiteEdgeCounts a)
    (P.no_incident_ties a) x y (P.initial a) t]

#print axioms trajectory_single_pair
#print axioms graphical_single_pair_twoTimeWeight

end ExceptionalTimes.PoissonDimerLaw
