import ExceptionalTimes.FiniteClockParallelStep

/-! Pathwise exact eventual count-grid approximations, allowing disjoint
simultaneous swaps. These are deterministic, not probability estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Classical Topology

namespace ExceptionalTimes.FiniteClockPointwiseGrid

open FiniteClockBridge FiniteClockSlicePath FiniteClockWordLaw FiniteClockGridLaw
open FiniteClockParallelStep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type*}

theorem trajectory_parallelWord_of_good (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    (edge : I → Site × Site)
    (hcover : ∀ u v t, C.Rings u v t → ∃ i, s(u,v) = pairIndex edge i)
    (η : Configuration) (h : ℝ) (hh : 0 ≤ h) (n : ℕ)
    (hgood : ∀ j : Fin n, ∃ τ, OneTimeSlice C ((j.val : ℝ)*h) (((j.val : ℝ)+1)*h) τ) :
    C.trajectory hf η ((n : ℝ)*h) =
      runWord (parallelUpdate edge) (gridWord C edge h n) η := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul,runWord] using ClockField.trajectory_zero ht hf η
  | succ n ih =>
    obtain ⟨τ,hτ⟩ := hgood (Fin.last n)
    have hstep := oneTimeSlice_colors C hc ht hf edge hcover η
      (mul_nonneg (Nat.cast_nonneg n) hh)
      (show (n : ℝ)*h ≤ ((n : ℝ)+1)*h by nlinarith) hτ
    rw [Nat.cast_add,Nat.cast_one,hstep,gridWord_snoc,runWord_snoc]
    rw [ih (fun j => hgood j.castSucc)]

/-- A finite mark-time set eventually has no two distinct elements in
the same grid slice. -/
theorem eventually_oneTimeSlice (C : ClockField) (T : Finset ℝ) (t : ℝ) (ht : 0 < t)
    (hT : ∀ u v r, C.Rings u v r → r ≤ t → r ∈ T) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin n,
      ∃ τ, OneTimeSlice C ((j.val : ℝ)*(t/n)) (((j.val : ℝ)+1)*(t/n)) τ := by
  have hsep : ∀ᶠ n : ℕ in atTop, ∀ r ∈ T, ∀ s ∈ T, r ≠ s → t/(n : ℝ) < |r-s| := by
    apply (eventually_all_finset T).mpr
    intro r hr
    apply (eventually_all_finset T).mpr
    intro s hs
    by_cases hrs : r = s
    · exact Eventually.of_forall (fun _ h => (h hrs).elim)
    · exact (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr hrs))) |>.mono (fun _ h _ => h)
  filter_upwards [hsep,eventually_ge_atTop 1] with n hn hpos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hstep : 0 < t/(n : ℝ) := div_pos ht hnpos
  intro j
  let a := (j.val : ℝ)*(t/n)
  let b := ((j.val : ℝ)+1)*(t/n)
  have hbt : b ≤ t := by
    have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
    calc
      b ≤ (n : ℝ)*(t/n) := mul_le_mul_of_nonneg_right hj hstep.le
      _ = t := mul_div_cancel₀ t hnpos.ne'
  by_cases hmark : ∃ u v r, C.Rings u v r ∧ a < r ∧ r ≤ b
  · obtain ⟨u,v,r,hr,har,hrb⟩ := hmark
    refine ⟨r,?_⟩
    intro x y s hs has hsb
    by_contra hsr
    have hsmall := hn s (hT x y s hs (hsb.trans hbt)) r (hT u v r hr (hrb.trans hbt)) hsr
    have hab : b-a = t/n := by dsimp [a,b]; ring
    have hdist : |s-r| ≤ t/n := by
      rw [abs_le]
      dsimp [a,b] at har hrb has hsb
      constructor <;> nlinarith
    exact (not_lt_of_ge hdist) hsmall
  · refine ⟨0,?_⟩
    intro u v r hr har hrb
    exact (hmark ⟨u,v,r,hr,har,hrb⟩).elim

theorem eventually_trajectory_parallelWord (C : ClockField) (hc : C.FiniteEdgeCounts)
    (hties : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    (edge : I → Site × Site)
    (hcover : ∀ u v t, C.Rings u v t → ∃ i, s(u,v) = pairIndex edge i)
    (T : Finset ℝ) (t : ℝ) (ht : 0 < t)
    (hT : ∀ u v r, C.Rings u v r → r ≤ t → r ∈ T) (η : Configuration) :
    ∀ᶠ n : ℕ in atTop, C.trajectory hf η t =
      runWord (parallelUpdate edge) (gridWord C edge (t/n) n) η := by
  filter_upwards [eventually_oneTimeSlice C T t ht hT,eventually_ge_atTop 1] with n hn hpos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have H := trajectory_parallelWord_of_good C hc hties hf edge hcover η (t/n)
    (div_pos ht hnpos).le n hn
  simpa only [mul_div_cancel₀ t hnpos.ne'] using H

variable [Fintype I]

theorem projected_parallelWord_of_good (V : Finset Site) (C : ClockField)
    (hc : C.FiniteEdgeCounts) (hties : C.NoIncidentTies) (edge : I → V × V)
    (η : Configuration) (t : ℝ) (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, projectedTrajectory V C hc edge η t =
      runWord (parallelCubeUpdate V edge) (gridWord C (siteEdges V edge) (t/n) n)
        (restrictColor V η) := by
  let F := retainedEdges V edge
  let T := F.biUnion (fun e => (hc e t).toFinset)
  have hcover : ∀ u v r, (C.restrictEdges F).Rings u v r →
      ∃ i, s(u,v) = pairIndex (siteEdges V edge) i := by
    intro u v r hr
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ((ClockField.restrictEdges_rings C F u v r).mp hr).1
    exact ⟨i,hi.symm⟩
  have hT : ∀ u v r, (C.restrictEdges F).Rings u v r → r ≤ t → r ∈ T := by
    intro u v r hr hrt
    obtain ⟨he,hr⟩ := (ClockField.restrictEdges_rings C F u v r).mp hr
    exact Finset.mem_biUnion.mpr ⟨s(u,v),he,(hc s(u,v) t).mem_toFinset.mpr ⟨hr,hr.pos,hrt⟩⟩
  have H := eventually_trajectory_parallelWord (C.restrictEdges F)
    (restricted_finite_counts C hc F) (hties.restrictEdges F)
    (ClockField.restrictEdges_hasFiniteBackwardTraces hc F) (siteEdges V edge) hcover T t ht hT η
  have hword (h : ℝ) (n : ℕ) : gridWord (C.restrictEdges F) (siteEdges V edge) h n =
      gridWord C (siteEdges V edge) h n := by
    ext j i
    apply restricted_markCount_of_mem
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  filter_upwards [H] with n hn
  unfold projectedTrajectory
  rw [hn,restrict_parallelWord,hword]

#print axioms eventually_oneTimeSlice
#print axioms projected_parallelWord_of_good

end ExceptionalTimes.FiniteClockPointwiseGrid
