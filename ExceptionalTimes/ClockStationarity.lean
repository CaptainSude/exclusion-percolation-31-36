import ExceptionalTimes.FiniteClockStationarity

/-! Full two-time stationarity for measurable finite-site events. The
finite-clock equality is transported to the literal infinite graphical
trajectory by pathwise stabilization of both observed time slices. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical Topology

namespace ExceptionalTimes.ClockStationarity

open FiniteClockBridge FiniteClockStationarity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem truncated_paired_stationary (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : Finset (Sym2 Site)) (A : Finset Site)
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    μ {ω | E (P.truncatedTrajectories F ω s) ∧ E (P.truncatedTrajectories F ω (s+t))} =
      μ {ω | E (P.initial ω) ∧ E (P.truncatedTrajectories F ω t)} := by
  let V := FiniteEdgeEnumeration.vertices F ∪ A
  have hv : FiniteEdgeEnumeration.vertices F ⊆ V := Finset.subset_union_left
  have ha : A ⊆ V := Finset.subset_union_right
  have H := projected_stationary V P (FiniteEdgeEnumeration.enumerate F V hv)
    (FiniteEdgeEnumeration.enumerate_injective F V hv) (fun _ => hr _) s t hs ht
    (fun η ξ => E (extendColor V η) ∧ E (extendColor V ξ))
  change μ {ω | E (extendColor V (restrictColor V
      (P.truncatedTrajectories (retainedEdges V (FiniteEdgeEnumeration.enumerate F V hv)) ω s))) ∧
    E (extendColor V (restrictColor V
      (P.truncatedTrajectories (retainedEdges V (FiniteEdgeEnumeration.enumerate F V hv)) ω (s+t))))} =
    μ {ω | E (extendColor V (restrictColor V (P.initial ω))) ∧
      E (extendColor V (restrictColor V
        (P.truncatedTrajectories (retainedEdges V (FiniteEdgeEnumeration.enumerate F V hv)) ω t)))} at H
  rw [FiniteEdgeEnumeration.enumerate_retainedEdges] at H
  simpa only [← FiniteMatchingComparison.frame_event_iff A V ha E hlocal] using H

theorem tendsto_truncated_paired_probability (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n) (A : Finset Site)
    (E : Configuration → Prop) (hE : MeasurableSet {η | E η})
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ)) (s t : ℝ) :
    Tendsto (fun n => μ {ω | E (P.truncatedTrajectories (F n) ω s) ∧
      E (P.truncatedTrajectories (F n) ω t)}) atTop
      (𝓝 (μ {ω | E (P.trajectories ω s) ∧ E (P.trajectories ω t)})) := by
  let : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  let test : Configuration → Configuration → ℝ≥0∞ := fun η ξ => if E η ∧ E ξ then 1 else 0
  have hm (n : ℕ) : NullMeasurableSet {ω | E (P.truncatedTrajectories (F n) ω s) ∧
      E (P.truncatedTrajectories (F n) ω t)} μ :=
    ((P.aemeasurable_truncated hr (F n) s).nullMeasurableSet_preimage hE).inter
      ((P.aemeasurable_truncated hr (F n) t).nullMeasurableSet_preimage hE)
  have hmfull : NullMeasurableSet {ω | E (P.trajectories ω s) ∧ E (P.trajectories ω t)} μ :=
    ((P.aemeasurable_trajectories_of_exhaustion hr F hmono hex s).nullMeasurableSet_preimage hE).inter
      ((P.aemeasurable_trajectories_of_exhaustion hr F hmono hex t).nullMeasurableSet_preimage hE)
  have htest : ∀ n, AEMeasurable
      (fun ω => test (P.truncatedTrajectories (F n) ω s) (P.truncatedTrajectories (F n) ω t)) μ := by
    intro n
    have hi := (aemeasurable_const (b := (1 : ℝ≥0∞))).indicator₀ (hm n)
    convert hi using 1
    funext ω
    simp [test,Set.indicator_apply]
  have hlim : Tendsto
      (fun n => ∫⁻ ω, test (P.truncatedTrajectories (F n) ω s) (P.truncatedTrajectories (F n) ω t) ∂μ)
      atTop (𝓝 (∫⁻ ω, test (P.trajectories ω s) (P.trajectories ω t) ∂μ)) := by
    apply tendsto_lintegral_of_dominated_convergence' (fun _ => 1) htest
    · intro n
      exact ae_of_all μ (fun ω => by dsimp [test]; split <;> simp)
    · simp
    · apply ae_of_all μ
      intro ω
      obtain ⟨N,hN⟩ := P.eventually_truncated_trajectory_eq F hmono hex ω s A
      obtain ⟨M,hM⟩ := P.eventually_truncated_trajectory_eq F hmono hex ω t A
      apply tendsto_atTop_of_eventually_const (i₀ := max N M)
      intro n hn
      have hs' := hlocal _ _ (hN n ((le_max_left N M).trans hn))
      have ht' := hlocal _ _ (hM n ((le_max_right N M).trans hn))
      change E (P.truncatedTrajectories (F n) ω s) ↔ E (P.trajectories ω s) at hs'
      change E (P.truncatedTrajectories (F n) ω t) ↔ E (P.trajectories ω t) at ht'
      simp only [test,hs',ht']
  have hl (n : ℕ) :
      (∫⁻ ω, test (P.truncatedTrajectories (F n) ω s) (P.truncatedTrajectories (F n) ω t) ∂μ) =
        μ {ω | E (P.truncatedTrajectories (F n) ω s) ∧ E (P.truncatedTrajectories (F n) ω t)} := by
    simpa only [Set.indicator,Set.mem_ofPred_eq,test,one_mul] using
      lintegral_indicator_const₀ (hm n) (1 : ℝ≥0∞)
  have hr' : (∫⁻ ω, test (P.trajectories ω s) (P.trajectories ω t) ∂μ) =
      μ {ω | E (P.trajectories ω s) ∧ E (P.trajectories ω t)} := by
    simpa only [Set.indicator,Set.mem_ofPred_eq,test,one_mul] using
      lintegral_indicator_const₀ hmfull (1 : ℝ≥0∞)
  simpa only [hl,hr'] using hlim

theorem paired_stationary_add_pos (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n) (A : Finset Site)
    (E : Configuration → Prop) (hE : MeasurableSet {η | E η})
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    μ {ω | E (P.trajectories ω s) ∧ E (P.trajectories ω (s+t))} =
      μ {ω | E (P.initial ω) ∧ E (P.trajectories ω t)} := by
  have H₁ := tendsto_truncated_paired_probability P hr F hmono hex A E hE hlocal s (s+t)
  have H₂ := tendsto_truncated_paired_probability P hr F hmono hex A E hE hlocal 0 t
  simp only [P.truncated_nonpos _ _ (le_refl 0),P.trajectories_zero] at H₂
  have H₃ := H₁.congr (fun n => truncated_paired_stationary P hr (F n) A E hlocal s t hs ht)
  exact tendsto_nhds_unique H₃ H₂

/-- Actual stationarity at every nonnegative starting time and lag. -/
theorem paired_stationary_add (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n) (A : Finset Site)
    (E : Configuration → Prop) (hE : MeasurableSet {η | E η})
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ {ω | E (P.trajectories ω s) ∧ E (P.trajectories ω (s+t))} =
      μ {ω | E (P.initial ω) ∧ E (P.trajectories ω t)} := by
  by_cases hs0 : s = 0
  · subst s
    simp only [zero_add,P.trajectories_zero]
  by_cases ht0 : t = 0
  · subst t
    simpa only [add_zero,P.trajectories_zero,and_self] using
      FiniteClockMarginal.preserves_local_event P hr F hmono hex A E hE hlocal s
  exact paired_stationary_add_pos P hr F hmono hex A E hE hlocal s t
    (lt_of_le_of_ne hs (Ne.symm hs0)) (lt_of_le_of_ne ht (Ne.symm ht0))

/-- The two-time stationarity hypothesis in the dimension reduction is
proved for every measurable event supported on finitely many sites. -/
theorem paired_stationary (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n) (A : Finset Site)
    (E : Configuration → Prop) (hE : MeasurableSet {η | E η})
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ {ω | E (P.trajectories ω s) ∧ E (P.trajectories ω t)} =
      μ {ω | E (P.trajectories ω 0) ∧ E (P.trajectories ω (dist s t))} := by
  rcases le_total s t with hst | hts
  · have H := paired_stationary_add P hr F hmono hex A E hE hlocal s (t-s) hs (sub_nonneg.mpr hst)
    have hd : dist s t = t-s := by rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hst)]; ring
    simpa only [add_sub_cancel,hd,P.trajectories_zero] using H
  · have H := paired_stationary_add P hr F hmono hex A E hE hlocal t (s-t) ht (sub_nonneg.mpr hts)
    have hd : dist s t = s-t := by rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hts)]
    simpa only [add_sub_cancel,hd,P.trajectories_zero,and_comm] using H

theorem oneArm_stationary (P : PoissonGraphicalRealization μ rate)
    (hr : ∀ e, 0 ≤ rate e) (F : ℕ → Finset (Sym2 Site))
    (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (v : Site) (R : ℕ) (hv : v ∈ latticeBox R) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ {ω | OneArm (P.trajectories ω s) v R ∧ OneArm (P.trajectories ω t) v R} =
      μ {ω | OneArm (P.trajectories ω 0) v R ∧ OneArm (P.trajectories ω (dist s t)) v R} :=
  paired_stationary P hr F hmono hex (latticeBox (R+1))
    (fun η => OneArm η v R) (measurableSet_oneArm v R)
    (fun _ _ heq => oneArm_congr_of_eqOn_box hv heq) s t hs ht

#print axioms truncated_paired_stationary
#print axioms tendsto_truncated_paired_probability
#print axioms oneArm_stationary

end ExceptionalTimes.ClockStationarity
