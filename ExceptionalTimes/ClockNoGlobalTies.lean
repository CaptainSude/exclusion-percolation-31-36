import ExceptionalTimes.FiniteClockGridLaw

/-! Independent Poisson count laws rule out simultaneous marks on
distinct edges almost surely. The proof uses finite interval counts,
without representing clocks by random exponential sequences. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical Topology

namespace ExceptionalTimes.ClockNoGlobalTies

open FiniteClockSlices FiniteClockGridLaw

theorem exists_grid_interval (h : ℝ) (n : ℕ) (t : ℝ)
    (ht : 0 < t) (htn : t ≤ n*h) :
    ∃ j : Fin n, (j.val : ℝ)*h < t ∧ t ≤ ((j.val : ℝ)+1)*h := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul] at htn; linarith
  | succ n ih =>
    by_cases hn : t ≤ n*h
    · obtain ⟨j,hj⟩ := ih hn
      exact ⟨j.castSucc,hj⟩
    · exact ⟨Fin.last n,lt_of_not_ge hn,by simpa only [Fin.val_last,Nat.cast_add,Nat.cast_one] using htn⟩

theorem GoodCounts.eq_of_nonzero {I : Type*} [Fintype I] [DecidableEq I]
    {c : I → ℕ} (hc : GoodCounts c) {i j : I} (hi : c i ≠ 0) (hj : c j ≠ 0) : i = j := by
  rcases hc with h0 | ⟨k,hk⟩
  · simp only [h0,Pi.zero_apply,ne_eq,not_true_eq_false] at hi
  · have hik : i = k := by
      by_contra hne
      simp [hk,hne] at hi
    have hjk : j = k := by
      by_contra hne
      simp [hk,hne] at hj
    exact hik.trans hjk.symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

theorem simultaneous_probability_zero (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (e f : Sym2 Site) (hef : e ≠ f) (T : ℝ) (hT : 0 < T) :
    μ {ω | ∃ t ≤ T, t ∈ (P.clocks ω).marks e ∧ t ∈ (P.clocks ω).marks f} = 0 := by
  let edge : Bool → Sym2 Site := fun b => if b then f else e
  have hinj : Function.Injective edge := by
    intro i j hij
    cases i <;> cases j <;> simp_all [edge]
  apply le_antisymm ?_ zero_le
  apply ge_of_tendsto (grid_error_bound_limit (∑ i,rate (edge i)) T)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  apply le_trans ?_ (graphical_grid_bad_probability_le P edge hinj
    (fun i => hr (edge i)) n (T/n) (div_pos hT hn0))
  apply measure_mono
  rintro ω ⟨t,htT,he,hf⟩
  have ht := (P.clocks ω).positive_time e t he
  obtain ⟨j,hj⟩ := exists_grid_interval (T/n) n t ht (by simpa only [mul_div_cancel₀ T hn0.ne'] using htT)
  refine ⟨j,?_⟩
  intro hgood
  have hnz (b : Bool) (hb : t ∈ (P.clocks ω).marks (edge b)) :
      (P.clocks ω).markCount (edge b) ((j.val : ℝ)*(T/n)) (((j.val : ℝ)+1)*(T/n)) ≠ 0 := by
    unfold ClockField.markCount
    rw [ne_eq,Set.ncard_eq_zero (P.finite_counts ω _ _ _)]
    exact Set.nonempty_iff_ne_empty.mp ⟨t,hb,hj⟩
  exact Bool.false_ne_true (GoodCounts.eq_of_nonzero hgood (hnz false he) (hnz true hf))

theorem ae_no_global_ties (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) :
    ∀ᵐ ω ∂μ, ∀ e f t, t ∈ (P.clocks ω).marks e → t ∈ (P.clocks ω).marks f → e = f := by
  have H : ∀ᵐ ω ∂μ, ∀ e f : Sym2 Site, ∀ n : ℕ,
      e ≠ f → ¬ ∃ t ≤ (n+1 : ℝ), t ∈ (P.clocks ω).marks e ∧ t ∈ (P.clocks ω).marks f := by
    rw [ae_all_iff]
    intro e
    rw [ae_all_iff]
    intro f
    rw [ae_all_iff]
    intro n
    by_cases hef : e = f
    · exact Filter.Eventually.of_forall (fun _ h => (h hef).elim)
    · have hzero := simultaneous_probability_zero P hr e f hef (n+1) (by positivity)
      have H : ∀ᵐ ω ∂μ, ¬ ∃ t ≤ (n+1 : ℝ),
          t ∈ (P.clocks ω).marks e ∧ t ∈ (P.clocks ω).marks f := by
        rw [ae_iff]
        simpa only [not_not] using hzero
      exact H.mono (fun _ h _ => h)
  filter_upwards [H] with ω hω
  intro e f t he hf
  by_contra hef
  obtain ⟨n,hn⟩ := exists_nat_gt t
  exact hω e f n hef ⟨t,by linarith,he,hf⟩

#print axioms ae_no_global_ties

end ExceptionalTimes.ClockNoGlobalTies
