import ExceptionalTimes.FiniteClockFutureLaw

/-! Count grids on an arbitrary time interval approximate the actual
finite graphical trajectory, initialized at its actual left endpoint. -/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical Topology

namespace ExceptionalTimes.FiniteClockShiftedGrid

open FiniteClockWordLaw FiniteClockBridge FiniteClockGridLaw FiniteClockSlices
open FiniteClockSlicePath FiniteClockFutureLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def shiftedWord (C : ClockField) (edge : I → Site × Site) (s h : ℝ) (n : ℕ) :
    Fin n → I → ℕ := fun j => sliceCounts C edge (s+(j.val : ℝ)*h) (s+((j.val : ℝ)+1)*h)

omit [Fintype I] [DecidableEq I] in
theorem shiftedWord_snoc (C : ClockField) (edge : I → Site × Site) (s h : ℝ) (n : ℕ) :
    shiftedWord C edge s h (n+1) = Fin.snoc (shiftedWord C edge s h n)
      (sliceCounts C edge (s+(n : ℝ)*h) (s+((n : ℝ)+1)*h)) := by
  ext j i
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [shiftedWord]
  · simp [shiftedWord]

/-- The same chronological update proof works after any nonnegative
initial time, on the event that each grid slice has at most one ring. -/
theorem trajectory_eq_shiftedWord_of_good (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    (edge : I → Site × Site)
    (hsupport : ∀ u v t, C.Rings u v t → ∃ i, s(u,v) = pairIndex edge i)
    (η : Configuration) (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) (n : ℕ)
    (hgood : ∀ j : Fin n, GoodCounts (shiftedWord C edge s h n j)) :
    C.trajectory hf η (s+(n : ℝ)*h) =
      runWord (countUpdate edge) (shiftedWord C edge s h n) (C.trajectory hf η s) := by
  induction n with
  | zero => simp [runWord]
  | succ n ih =>
    have hstep := goodSlice_colors C hc ht hf edge hsupport η
      (add_nonneg hs (mul_nonneg (Nat.cast_nonneg n) hh))
      (show s+(n : ℝ)*h ≤ s+((n : ℝ)+1)*h by nlinarith)
      (hgood (Fin.last n))
    change C.trajectory hf η (s+((n : ℝ)+1)*h) =
      countUpdate edge (sliceCounts C edge (s+(n : ℝ)*h) (s+((n : ℝ)+1)*h))
        (C.trajectory hf η (s+(n : ℝ)*h)) at hstep
    rw [Nat.cast_add,Nat.cast_one,hstep,shiftedWord_snoc,runWord_snoc]
    rw [ih (fun j => hgood j.castSucc)]

theorem projected_eq_shiftedWord_of_good (V : Finset Site)
    (C : ClockField) (hc : C.FiniteEdgeCounts) (ht : C.NoIncidentTies)
    (edge : I → V × V) (η : Configuration) (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) (n : ℕ)
    (hgood : ∀ j : Fin n, GoodCounts (shiftedWord C (siteEdges V edge) s h n j)) :
    projectedTrajectory V C hc edge η (s+(n : ℝ)*h) =
      runWord (cubeUpdate V edge) (shiftedWord C (siteEdges V edge) s h n)
        (projectedTrajectory V C hc edge η s) := by
  let F := retainedEdges V edge
  have hsupp : ∀ u v t, (C.restrictEdges F).Rings u v t → ∃ i,
      s(u,v) = pairIndex (siteEdges V edge) i := by
    intro u v t hr
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ((ClockField.restrictEdges_rings C F u v t).mp hr).1
    exact ⟨i,hi.symm⟩
  have hcounts (a b : ℝ) : sliceCounts (C.restrictEdges F) (siteEdges V edge) a b =
      sliceCounts C (siteEdges V edge) a b := by
    funext i
    apply restricted_markCount_of_mem
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hw : shiftedWord (C.restrictEdges F) (siteEdges V edge) s h n =
      shiftedWord C (siteEdges V edge) s h n := by
    funext j
    exact hcounts _ _
  have hpath := trajectory_eq_shiftedWord_of_good (C.restrictEdges F)
    (restricted_finite_counts C hc F) (ht.restrictEdges F)
    (ClockField.restrictEdges_hasFiniteBackwardTraces hc F)
    (siteEdges V edge) hsupp η s h hs hh n (by simpa only [hw] using hgood)
  unfold projectedTrajectory
  rw [hpath,restrictColor_runWord,hw]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

/-- The discrepancy estimate is independent of the left endpoint. -/
theorem shifted_bad_probability_le (P : PoissonGraphicalRealization μ rate)
    (edge : I → Sym2 Site) (hinj : Function.Injective edge) (hr : ∀ i, 0 ≤ rate (edge i))
    (s h : ℝ) (hs : 0 ≤ s) (hh : 0 < h) (n : ℕ) :
    μ {ω | ∃ j : Fin n, ¬GoodCounts
      (fun i => (P.clocks ω).markCount (edge i) (s+(j.val : ℝ)*h) (s+((j.val : ℝ)+1)*h))} ≤
      (n : ℝ≥0∞)*ENNReal.ofReal (((∑ i,rate (edge i))*h)^2) := by
  let _ : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  have hb := any_bad_probability_le n
    (fun ω j i => (P.clocks ω).markCount (edge i) (s+(j.val : ℝ)*h) (s+((j.val : ℝ)+1)*h))
    (fun j => Measurable.of_eval (fun i => P.measurable_counts _ _ _))
    (fun i => rate (edge i)*h) (fun i => mul_nonneg (hr i) hh.le)
    (fun j => by
      have hL := slice_count_law P.independent_law edge hinj (s+(j.val : ℝ)*h) h
        (add_nonneg hs (mul_nonneg (Nat.cast_nonneg _) hh.le)) hh
      simpa only [add_mul,one_mul,add_assoc] using hL)
  simpa only [← Finset.sum_mul] using hb

noncomputable def shiftedApprox (V : Finset Site) (P : PoissonGraphicalRealization μ rate)
    (edge : I → V × V) (s h : ℝ) (n : ℕ) (ω : Ω) : V → Bool :=
  runWord (cubeUpdate V edge) (shiftedWord (P.clocks ω) (siteEdges V edge) s h n)
    (projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) s)

theorem shifted_discrepancy_le (V : Finset Site) (P : PoissonGraphicalRealization μ rate)
    (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (s h : ℝ) (hs : 0 ≤ s) (hh : 0 < h) (n : ℕ) :
    μ {ω | projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω)
        (s+(n : ℝ)*h) ≠ shiftedApprox V P edge s h n ω} ≤
      (n : ℝ≥0∞)*ENNReal.ofReal (((∑ i,rate (edgePair V edge i))*h)^2) := by
  apply le_trans (measure_mono (t := {ω | ∃ j : Fin n,
    ¬GoodCounts (shiftedWord (P.clocks ω) (siteEdges V edge) s h n j)}) ?_)
    (shifted_bad_probability_le P (edgePair V edge) hinj hr s h hs hh n)
  intro ω hne
  by_contra hn
  have hgood : ∀ j : Fin n, GoodCounts (shiftedWord (P.clocks ω) (siteEdges V edge) s h n j) := by
    intro j
    by_contra hj
    exact hn ⟨j,hj⟩
  exact hne (projected_eq_shiftedWord_of_good V (P.clocks ω) (P.finiteEdgeCounts ω)
    (P.no_incident_ties ω) edge (P.initial ω) s h hs hh.le n hgood)

theorem tendsto_shifted_discrepancy (V : Finset Site) (P : PoissonGraphicalRealization μ rate)
    (edge : I → V × V) (hinj : Function.Injective (edgePair V edge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t) :
    Tendsto (fun n : ℕ => μ {ω | projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω)
      edge (P.initial ω) (s+t) ≠ shiftedApprox V P edge s (t/n) n ω}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (grid_error_bound_limit (∑ i,rate (edgePair V edge i)) t)
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have H := shifted_discrepancy_le V P edge hinj hr s (t/n) hs (div_pos ht hn') n
  simpa only [mul_div_cancel₀ t hn'.ne'] using H

#print axioms projected_eq_shiftedWord_of_good
#print axioms tendsto_shifted_discrepancy

end ExceptionalTimes.FiniteClockShiftedGrid

