import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Centered finite signed block kernels force ordinary Boolean influence.
The test may couple all block histories arbitrarily. No monotonicity of the
outer real function, probability law, or independence of an exterior is used. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.CenteredBlocks

variable {I : Type*} [Fintype I] {H : I → Type*} [∀ i, Fintype (H i)]

/-- The literal finite product signed integral. -/
noncomputable def kernel (w : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) : ℝ :=
  ∑ h, (∏ i, w i (h i)) * f h

/-- Sum of absolute masses of a finite signed law. -/
noncomputable def variation {A : Type*} [Fintype A] (w : A → ℝ) : ℝ := ∑ a, |w a|

/-- Splitting out one selected history in a genuinely signed integral. -/
theorem kernel_split (w : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) (i : I) :
    kernel w f = ∑ o : ∀ j : {j // j ≠ i}, H j,
      (∏ j : {j // j ≠ i}, w j (o j)) *
        ∑ a : H i, w i a * f ((Equiv.piSplitAt i H).symm (a, o)) := by
  unfold kernel
  rw [← Equiv.sum_comp (Equiv.piSplitAt i H).symm, Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have hi : (Equiv.piSplitAt i H).symm (a, o) i = a := by simp [Equiv.piSplitAt]
  have ho : ∀ j : {j // j ≠ i}, (Equiv.piSplitAt i H).symm (a, o) j = o j := by
    intro j
    simp [Equiv.piSplitAt, j.property]
  simp only [hi, ho]
  ring

/-- Centering annihilates a test which is constant in any selected block. -/
theorem kernel_zero_of_block_constant (w : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ)
    (i : I) (hw : ∑ a, w i a = 0)
    (hf : ∀ h a, f (Function.update h i a) = f h) : kernel w f = 0 := by
  by_cases hempty : IsEmpty (H i)
  · let := hempty
    simp [kernel_split w f i]
  · have : Nonempty (H i) := not_isEmpty_iff.mp hempty
    let a0 : H i := Classical.choice inferInstance
    rw [kernel_split]
    apply Finset.sum_eq_zero
    intro o _
    have he (a : H i) : f ((Equiv.piSplitAt i H).symm (a, o)) =
        f ((Equiv.piSplitAt i H).symm (a0, o)) := by
      have hu : Function.update ((Equiv.piSplitAt i H).symm (a0, o)) i a =
          (Equiv.piSplitAt i H).symm (a, o) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [Equiv.piSplitAt]
        · simp [Equiv.piSplitAt, hj]
      rw [← hu]
      exact hf _ _
    simp_rw [he]
    rw [← Finset.sum_mul, hw, zero_mul, mul_zero]

/-- A nonzero signed kernel needs a changing assignment in every centered block. -/
theorem nonzero_block_witness (w : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ)
    (hw : ∀ i, ∑ a, w i a = 0) (hk : kernel w f ≠ 0) (i : I) :
    ∃ h a, f (Function.update h i a) ≠ f h := by
  by_contra hn
  apply hk
  apply kernel_zero_of_block_constant w f i (hw i)
  intro h a
  exact not_not.mp (fun hne => hn ⟨h, a, hne⟩)

/-- A changing arbitrary real function of a test vector forces one of the
tested Boolean coordinates to change. The outer function need not be monotone. -/
theorem nonzero_test_witness {J : Type*} (w : ∀ i, H i → ℝ)
    (test : (∀ i, H i) → J → Bool) (outer : (J → Bool) → ℝ)
    (hw : ∀ i, ∑ a, w i a = 0) (hk : kernel w (fun h => outer (test h)) ≠ 0) (i : I) :
    ∃ h a j, test (Function.update h i a) j ≠ test h j := by
  obtain ⟨h, a, ha⟩ := nonzero_block_witness w _ hw hk i
  by_contra hn
  apply ha
  congr 1
  funext j
  exact not_not.mp (fun hj => hn ⟨h, a, j, hj⟩)

/-- Product total variation bounds the signed integral of every bounded test. -/
theorem kernel_variation_bound (w : ∀ i, H i → ℝ) (f : (∀ i, H i) → ℝ) (M : ℝ)
    (hf : ∀ h, |f h| ≤ M) : |kernel w f| ≤ (∏ i, variation (w i)) * M := by
  calc
    |kernel w f| ≤ ∑ h, |(∏ i, w i (h i)) * f h| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ h, (∏ i, |w i (h i)|) * |f h| := by simp only [abs_mul, Finset.abs_prod]
    _ ≤ ∑ h, (∏ i, |w i (h i)|) * M := Finset.sum_le_sum
      (fun h _ => mul_le_mul_of_nonneg_left (hf h) (Finset.prod_nonneg (fun _ _ => abs_nonneg _)))
    _ = (∏ i, variation (w i)) * M := by
      rw [← Finset.sum_mul, ← Fintype.prod_sum (fun i a => |w i a|)]
      rfl

def AllBlocksInfluential {J : Type*} (test : (∀ i, H i) → J → Bool) : Prop :=
  ∀ i, ∃ h a j, test (Function.update h i a) j ≠ test h j

/-- A support estimate with one necessary event, without a union over all assignments. -/
theorem kernel_variation_support {J : Type*} (w : ∀ i, H i → ℝ)
    (test : (∀ i, H i) → J → Bool) (outer : (J → Bool) → ℝ) (M : ℝ)
    (hw : ∀ i, ∑ a, w i a = 0) (hf : ∀ h, |outer (test h)| ≤ M) :
    |kernel w (fun h => outer (test h))| ≤ (∏ i, variation (w i)) * M *
      (if AllBlocksInfluential test then 1 else 0) := by
  by_cases hs : AllBlocksInfluential test
  · rw [ite_eq_left hs, mul_one]
    exact kernel_variation_bound w _ M hf
  · have hz : kernel w (fun h => outer (test h)) = 0 := by
      by_contra hn
      exact hs (nonzero_test_witness w test outer hw hn)
    simp [hz, hs]

/-- Pointwise support bounds can be averaged over an arbitrary finite exterior.
No relation between that exterior and the tested crossing functions is assumed. -/
theorem exterior_variation_support {O J : Type*} [Fintype O]
    (μ : O → ℝ) (hμ : ∀ o, 0 ≤ μ o) (w : ∀ _o : O, ∀ i, H i → ℝ)
    (test : O → (∀ i, H i) → J → Bool) (outer : O → (J → Bool) → ℝ) (M : O → ℝ)
    (hw : ∀ o i, ∑ a, w o i a = 0) (hf : ∀ o h, |outer o (test o h)| ≤ M o) :
    (∑ o, μ o * |kernel (w o) (fun h => outer o (test o h))|) ≤
      ∑ o, μ o * ((∏ i, variation (w o i)) * M o *
        (if AllBlocksInfluential (test o) then 1 else 0)) :=
  Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left
    (kernel_variation_support (w o) (test o) (outer o) (M o) (hw o) (hf o)) (hμ o))

section PairHistories

abbrev PairColor := Fin 2 → Bool

theorem pair_update_endpoints (a b : PairColor) :
    Function.update (Function.update a 0 (b 0)) 1 (b 1) = b := by
  funext e
  fin_cases e <;> simp

theorem change_to_flip (f : PairColor → Bool) (c : PairColor) (e : Fin 2) (b : Bool)
    (hf : f (Function.update c e b) ≠ f c) :
    f (Function.update c e (!(c e))) ≠ f c := by
  have hb : b ≠ c e := by
    intro he
    rw [he, Function.update_eq_self] at hf
    exact hf rfl
  have hflip : b = !(c e) := by
    cases hc : c e <;> cases b <;> simp_all
  rw [← hflip]
  exact hf

/-- Interpolation through the two endpoints produces an ordinary single-bit pivotal
flip. This interpolation is not required to be an allowed dynamical update. -/
theorem pair_flip_witness (f : PairColor → Bool) (a b : PairColor) (hf : f b ≠ f a) :
    ∃ c e, f (Function.update c e (!(c e))) ≠ f c := by
  let c := Function.update a 0 (b 0)
  by_cases h0 : f c = f a
  · have h1 : f (Function.update c 1 (b 1)) ≠ f c := by
      dsimp [c]
      rw [pair_update_endpoints]
      exact fun h => hf (h.trans h0)
    exact ⟨c, 1, change_to_flip f c 1 (b 1) h1⟩
  · exact ⟨a, 0, change_to_flip f a 0 (b 0) h0⟩

variable {T : Type*} [Fintype T] [DecidableEq T]

def slice (h : I → T → PairColor) (t : T) : I → PairColor := fun i => h i t

noncomputable def flipHistory (h : I → T → PairColor) (i : I) (t : T) (e : Fin 2) : I → T → PairColor :=
  Function.update h i (Function.update (h i) t (Function.update (h i t) e (!(h i t e))))

omit [Fintype I] [Fintype T] [DecidableEq T] in
theorem slice_update (h : I → T → PairColor) (i : I) (a : T → PairColor) (t : T) :
    slice (Function.update h i a) t = Function.update (slice h t) i (a t) := by
  funext j
  by_cases hj : j = i <;> simp [slice, hj]

omit [Fintype I] [Fintype T] in
theorem slice_flipHistory (h : I → T → PairColor) (i : I) (t : T) (e : Fin 2) :
    slice (flipHistory h i t e) t =
      Function.update (slice h t) i (Function.update (h i t) e (!(h i t e))) := by
  simp [flipHistory, slice_update]

omit [Fintype I] [Fintype T] in
theorem flipHistory_other_block (h : I → T → PairColor) (i j : I) (t : T) (e : Fin 2)
    (hj : j ≠ i) : flipHistory h i t e j = h j := by simp [flipHistory, hj]

omit [Fintype I] [Fintype T] in
theorem flipHistory_other_time (h : I → T → PairColor) (i : I) (t u : T) (e : Fin 2)
    (hu : u ≠ t) : flipHistory h i t e i u = h i u := by simp [flipHistory, hu]

omit [Fintype I] [Fintype T] in
theorem flipHistory_other_endpoint (h : I → T → PairColor) (i : I) (t : T) (e v : Fin 2)
    (hv : v ≠ e) : flipHistory h i t e i t v = h i t v := by simp [flipHistory, hv]

/-- The finite vector of tested crossings, with its time coordinate explicit. -/
def historyTests {Q : Type*} (cross : Q → T → (I → PairColor) → Bool)
    (h : I → T → PairColor) (qt : Q × T) : Bool := cross qt.1 qt.2 (slice h qt.2)

/-- Every centered block in a nonzero kernel has an ordinary endpoint pivotal
witness for a tested crossing at one of the tested times. The witness for one
block need not be the witness for another block. -/
theorem pair_history_pivotal_witness {Q : Type*}
    (w : I → (T → PairColor) → ℝ) (cross : Q → T → (I → PairColor) → Bool)
    (outer : (Q × T → Bool) → ℝ) (hw : ∀ i, ∑ a, w i a = 0)
    (hk : kernel w (fun h => outer (historyTests cross h)) ≠ 0) (i : I) :
    ∃ z q t e, cross q t (slice (flipHistory z i t e) t) ≠ cross q t (slice z t) := by
  obtain ⟨h, a, ⟨q, t⟩, ha⟩ := nonzero_test_witness w (historyTests cross) outer hw hk i
  let f : PairColor → Bool := fun c => cross q t (Function.update (slice h t) i c)
  have hself : Function.update (slice h t) i (h i t) = slice h t := by
    change Function.update (slice h t) i ((slice h t) i) = slice h t
    simp
  have hf : f (a t) ≠ f (h i t) := by
    simpa only [f, historyTests, slice_update, hself] using ha
  obtain ⟨c, e, he⟩ := pair_flip_witness f (h i t) (a t) hf
  let z : I → T → PairColor := Function.update h i (Function.update (h i) t c)
  refine ⟨z, q, t, e, ?_⟩
  simpa [slice_flipHistory, z, slice_update, f] using he

def AllEndpointPivotal {Q : Type*} (cross : Q → T → (I → PairColor) → Bool) : Prop :=
  ∀ i, ∃ z q t e, cross q t (slice (flipHistory z i t e) t) ≠ cross q t (slice z t)

/-- Total variation is charged only to the necessary pivotal-probe event,
with no sum over the possible interpolation assignments. -/
theorem pair_kernel_variation_support {Q : Type*}
    (w : I → (T → PairColor) → ℝ) (cross : Q → T → (I → PairColor) → Bool)
    (outer : (Q × T → Bool) → ℝ) (M : ℝ) (hw : ∀ i, ∑ a, w i a = 0)
    (hf : ∀ h, |outer (historyTests cross h)| ≤ M) :
    |kernel w (fun h => outer (historyTests cross h))| ≤
      (∏ i, variation (w i)) * M * (if AllEndpointPivotal cross then 1 else 0) := by
  by_cases hs : AllEndpointPivotal cross
  · rw [ite_eq_left hs, mul_one]
    exact kernel_variation_bound w _ M hf
  · have hz : kernel w (fun h => outer (historyTests cross h)) = 0 := by
      by_contra hn
      exact hs (pair_history_pivotal_witness w cross outer hw hn)
    simp [hz, hs]

/-- The actual two-time pair-history specialization. Each block supplies its
own test, time, background assignment, and pivotal endpoint. -/
theorem two_time_pair_pivotal {Q : Type*}
    (w : I → (Fin 2 → PairColor) → ℝ)
    (cross : Q → Fin 2 → (I → PairColor) → Bool)
    (outer : (Q × Fin 2 → Bool) → ℝ) (hw : ∀ i, ∑ a, w i a = 0)
    (hk : kernel w (fun h => outer (historyTests cross h)) ≠ 0) :
    AllEndpointPivotal cross :=
  pair_history_pivotal_witness w cross outer hw hk

/-- The full signed expectation obeys a single necessary-event support bound.
The exterior law and all signed masses may depend on the exterior value. -/
theorem exterior_pair_variation_support {O Q : Type*} [Fintype O]
    (μ : O → ℝ) (hμ : ∀ o, 0 ≤ μ o)
    (w : O → I → (T → PairColor) → ℝ)
    (cross : O → Q → T → (I → PairColor) → Bool)
    (outer : O → (Q × T → Bool) → ℝ) (M : O → ℝ)
    (hw : ∀ o i, ∑ a, w o i a = 0)
    (hf : ∀ o h, |outer o (historyTests (cross o) h)| ≤ M o) :
    |∑ o, μ o * kernel (w o) (fun h => outer o (historyTests (cross o) h))| ≤
      ∑ o, μ o * ((∏ i, variation (w o i)) * M o *
        (if AllEndpointPivotal (cross o) then 1 else 0)) := by
  calc
    _ ≤ ∑ o, |μ o * kernel (w o) (fun h => outer o (historyTests (cross o) h))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ o, μ o * |kernel (w o) (fun h => outer o (historyTests (cross o) h))| := by
      apply Finset.sum_congr rfl
      intro o _
      rw [abs_mul, abs_of_nonneg (hμ o)]
    _ ≤ _ := Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left
      (pair_kernel_variation_support (w o) (cross o) (outer o) (M o) (hw o) (hf o)) (hμ o))

end PairHistories

#print axioms nonzero_test_witness
#print axioms pair_history_pivotal_witness
#print axioms two_time_pair_pivotal
#print axioms exterior_pair_variation_support

end ExceptionalTimes.CenteredBlocks
