import ExceptionalTimes.DimerSingleton

/-! Exact pivotal normalization for endpoint refresh. These identities
hold for arbitrary Boolean tests, without monotonicity or asymptotics. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.DimerPivotalCalibration

open PairSquareSewing DimerLaw DimerExpansion DimerSelectedDictionary DimerBaseField
open DimerSingleton DimerJumpCalibration CenteredBlocks BlockExpansion EnvironmentVariance
open ProbeProduct ActivePartitionLaw CanonicalSpatialProduct FiniteHaar

noncomputable section
variable {B : Type*} [Fintype B]

omit [Fintype B] in
theorem overwrite_singleton_update {A : Type*} (b : B) (x : B → A) (a : A) :
    SelectedKernelLaw.overwrite {b} x (fun _ => a)=Function.update x b a := by
  funext j
  by_cases hj : j=b
  · subst j
    exact (SelectedKernelLaw.join_inside {b} (fun _ => a) (fun j => x j) ⟨b,by simp⟩).trans
      (Function.update_self b a x).symm
  · have h := SelectedKernelLaw.join_outside {b} (fun _ => a) (fun j => x j) ⟨j,by simpa⟩
    exact h.trans (Function.update_of_ne hj a x).symm

theorem selected_singleton_average (b : B) (u : History → ℝ)
    (F : ((B → Color)×(B → Color)) → ℝ) :
    selectedKernel (fun _ : B => base) (fun _ => u) {b}
      (fun h => F (pairCoordinates.symm h))=
      average (fun x : B → Color => ∑ h : History,u h*
        F (Function.update x b h.1,Function.update x b h.2)) := by
  rw [show (fun _ : B => base)=(fun _ h => twoTimeWeight 0 h.1 h.2) from rfl]
  rw [SelectedKernelLaw.canonical_selected_coefficient (fun _ : B => 0)
    (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => u) {b} F]
  rw [manyLaw_zero_expect]
  apply congrArg average
  funext x
  rw [singleton_kernel]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  congr 1
  apply congrArg F
  rw [overwrite_singleton_update]
  apply Prod.ext <;> funext j
  all_goals
    by_cases hj : j=b
    · subst j; simp [pairCoordinates]
    · simp [pairCoordinates,Function.update_of_ne hj]

theorem average_pi_split {A : Type*} [Fintype A] (b : B) (f : (B → A) → ℝ) :
    average f=average (fun a : A => average (fun o : {j : B // j≠b} → A =>
      f ((Equiv.piSplitAt b (fun _ : B => A)).symm (a,o)))) := by
  rw [←average_equiv (Equiv.piSplitAt b (fun _ : B => A)).symm f]
  exact FiniteSiteLaw.average_prod _

theorem average_update {A : Type*} [Fintype A] [Nonempty A]
    (b : B) (f : (B → A) → ℝ) :
    average (fun x : B → A => average (fun a => f (Function.update x b a)))=average f := by
  rw [average_pi_split b]
  have hu (s a : A) (o : {j : B // j≠b} → A) :
      Function.update ((Equiv.piSplitAt b (fun _ : B => A)).symm (s,o)) b a=
        (Equiv.piSplitAt b (fun _ : B => A)).symm (a,o) := by
    funext j
    by_cases hj : j=b
    · subst j; simp [Equiv.piSplitAt]
    · simp [Equiv.piSplitAt,hj]
  simp only [hu,average_const]
  rw [average_comm,←average_pi_split b]

theorem refresh_jump_table (f : Color → Bool) :
    (∑ h : History,refreshInsertion h*indicator (f h.1≠f h.2))=
      (1/4:ℝ)*average (fun a : Color => ∑ e : Fin 2,
        indicator (f (Function.update a e false)≠f (Function.update a e true))) := by
  have hup (a b : Bool) (e : Fin 2) (c : Bool) :
      Function.update (pair a b) e c=if e=0 then pair c b else pair a c := by
    funext j
    fin_cases e <;> fin_cases j <;> simp [pair]
  simp only [Fintype.sum_prod_type,sum_color,average_color,Fin.sum_univ_succ,hup]
  cases h00 : f (pair false false) <;> cases h01 : f (pair false true) <;>
    cases h10 : f (pair true false) <;> cases h11 : f (pair true true) <;>
      simp_all [refreshInsertion,siteInsertion,siteBase,indicator,pair] <;> norm_num

def pivotal (C : (B → Color) → Bool) (b : B) (e : Fin 2) (x : B → Color) : ℝ :=
  indicator (C (Function.update x b (Function.update (x b) e false))≠
    C (Function.update x b (Function.update (x b) e true)))

theorem singleton_refresh_pivotal (b : B) (C : (B → Color) → Bool) :
    selectedKernel (fun _ : B => base) (fun _ => refreshInsertion) {b}
      (fun h => indicator (C (pairCoordinates.symm h).1≠C (pairCoordinates.symm h).2))=
      (1/4:ℝ)*average (fun x => ∑ e,pivotal C b e x) := by
  rw [selected_singleton_average b refreshInsertion (fun xy => indicator (C xy.1≠C xy.2))]
  have ht (x : B → Color) := refresh_jump_table (fun a => C (Function.update x b a))
  have he : (fun x : B → Color => ∑ h : History,refreshInsertion h*
      indicator (C (Function.update x b h.1)≠C (Function.update x b h.2)))=
      (fun x : B → Color => (1/4:ℝ)*average (fun a : Color => ∑ e : Fin 2,
        indicator (C (Function.update x b (Function.update a e false))≠
          C (Function.update x b (Function.update a e true))))) := funext ht
  rw [he]
  rw [average_const_mul]
  congr 1
  have hu (x : B → Color) (a : Color) :
      (∑ e : Fin 2,indicator (C (Function.update x b (Function.update a e false))≠
        C (Function.update x b (Function.update a e true))))=
      ∑ e,pivotal C b e (Function.update x b a) := by
    simp [pivotal]
  simp_rw [hu]
  exact average_update b (fun x => ∑ e,pivotal C b e x)

#print axioms singleton_refresh_pivotal

end
end ExceptionalTimes.DimerPivotalCalibration
