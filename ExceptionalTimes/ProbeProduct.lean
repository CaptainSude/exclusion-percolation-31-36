import ExceptionalTimes.CenteredBlocks
import ExceptionalTimes.EnvironmentVariance
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
Centered signed kernels tested against a literal independent finite exterior.
The exterior consists of disjoint probe-coordinate blocks and an unused block.
The product probability and finite union costs are proved. The geometric input
is explicitly the local implication from endpoint-pivotal witnesses to necessary
probe events; its planar arm extraction and disjoint-site construction are not
asserted here. Individual probe bounds may be supplied by static arm estimates.
-/

open scoped BigOperators Classical

namespace ExceptionalTimes.ProbeProduct

open EnvironmentVariance CenteredBlocks

theorem indicator_forall {A : Type*} [Fintype A] (E : A → Prop) :
    indicator (∀ a, E a) = ∏ a, indicator (E a) := by
  by_cases h : ∀ a, E a
  · simp [indicator, h]
  · obtain ⟨a, ha⟩ : ∃ a, ¬ E a := by simpa using h
    rw [indicator, ite_eq_right h]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [indicator, ha])

theorem probability_pi {A : Type*} [Fintype A] [DecidableEq A]
    {Ξ : A → Type*} [∀ a, Fintype (Ξ a)] (ν : ∀ a, FiniteLaw (Ξ a))
    (E : ∀ a, Ξ a → Prop) :
    probability (FiniteLaw.pi ν) (fun x => ∀ a, E a (x a)) = ∏ a, probability (ν a) (E a) := by
  simp only [probability, FiniteLaw.expect, FiniteLaw.pi, indicator_forall,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun a x => (ν a).weight x * indicator (E a x))).symm

theorem indicator_exists_le {C : Type*} [Fintype C] (E : C → Prop) :
    indicator (∃ c, E c) ≤ ∑ c, indicator (E c) := by
  by_cases h : ∃ c, E c
  · obtain ⟨c, hc⟩ := h
    have hs := Finset.single_le_sum (f := fun c => indicator (E c))
      (fun c _ => indicator_nonneg (E c)) (Finset.mem_univ c)
    have hex : ∃ c, E c := ⟨c, hc⟩
    calc
      _ = indicator (E c) := by simp [indicator, hex, hc]
      _ ≤ _ := hs
  · rw [indicator, ite_eq_right h]
    exact Finset.sum_nonneg (fun c _ => indicator_nonneg (E c))

/-- Only the finite tested-quad/time/endpoint choice set is union-bounded. -/
theorem probability_exists_le {Ξ C : Type*} [Fintype Ξ] [Fintype C]
    (ν : FiniteLaw Ξ) (E : C → Ξ → Prop) :
    probability ν (fun x => ∃ c, E c x) ≤ ∑ c, probability ν (E c) := by
  calc
    _ ≤ ν.expect (fun x => ∑ c, indicator (E c x)) :=
      ν.expect_mono (fun x => indicator_exists_le (fun c => E c x))
    _ = _ := by
      simp only [FiniteLaw.expect, probability, Finset.mul_sum]
      exact Finset.sum_comm

variable {A Z : Type*} [Fintype A] [DecidableEq A] [Fintype Z]
variable {Ξ : A → Type*} [∀ a, Fintype (Ξ a)]

/-- Independent probe blocks plus arbitrary unused exterior coordinates. -/
noncomputable def probeLaw (ν₀ : FiniteLaw Z) (ν : ∀ a, FiniteLaw (Ξ a)) :
    FiniteLaw (Z × (∀ a, Ξ a)) := ν₀.prod (FiniteLaw.pi ν)

theorem probability_probeLaw (ν₀ : FiniteLaw Z) (ν : ∀ a, FiniteLaw (Ξ a))
    (E : ∀ a, Ξ a → Prop) :
    probability (probeLaw ν₀ ν) (fun o => ∀ a, E a (o.2 a)) =
      ∏ a, probability (ν a) (E a) := by
  unfold probability probeLaw
  rw [FiniteLaw.expect_prod]
  change ν₀.expect (fun _ => probability (FiniteLaw.pi ν) (fun x => ∀ a, E a (x a))) = _
  rw [FiniteLaw.expect_const]
  exact probability_pi ν E

section FairSites

/-- The normalized law of one actual fair Boolean color. -/
noncomputable def fairBit : FiniteLaw Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by simp

/-- Independent fair colors on a finite site set. -/
noncomputable def fairSites (D : Type*) [Fintype D] [DecidableEq D] : FiniteLaw (D → Bool) :=
  FiniteLaw.pi (fun _ : D => fairBit)

def relabelColors {D E : Type*} (e : D ≃ E) : (D → Bool) ≃ (E → Bool) where
  toFun ω y := ω (e.symm y)
  invFun η x := η (e x)
  left_inv ω := by funext x; simp
  right_inv η := by funext y; simp

/-- A concrete bijection of site labels preserves the original iid fair law. -/
theorem fairSites_relabel {D E : Type*} [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E] (e : D ≃ E) (f : (E → Bool) → ℝ) :
    (fairSites D).expect (fun ω => f (relabelColors e ω)) = (fairSites E).expect f := by
  unfold FiniteLaw.expect
  rw [← (relabelColors e).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  change (∏ d : D, (1 / 2 : ℝ)) = ∏ y : E, (1 / 2 : ℝ)
  exact e.prod_comp (fun _ => (1 / 2 : ℝ))

variable {U : Type*} {S : A → Type*} [Fintype U] [DecidableEq U]
variable [∀ a, Fintype (S a)] [∀ a, DecidableEq (S a)]

/-- Sites in separate probes and the unused exterior are genuinely disjoint
coordinates. The equivalence simply groups the original site colors. -/
def splitSites : ((U ⊕ Sigma S) → Bool) ≃ ((U → Bool) × (∀ a, S a → Bool)) where
  toFun ω := (fun u => ω (.inl u), fun a s => ω (.inr ⟨a, s⟩))
  invFun o := Sum.elim o.1 (fun s => o.2 s.1 s.2)
  left_inv ω := by
    funext s
    rcases s with u | ⟨a, s⟩ <;> rfl
  right_inv _ := rfl

/-- Grouping independent fair site colors produces exactly `probeLaw`.
Thus the probe independence used below is derived from the iid site law. -/
theorem fairSites_split_expect (f : ((U → Bool) × (∀ a, S a → Bool)) → ℝ) :
    (fairSites (U ⊕ Sigma S)).expect (fun ω => f (splitSites ω)) =
      (probeLaw (fairSites U) (fun a => fairSites (S a))).expect f := by
  unfold FiniteLaw.expect
  rw [← (splitSites (U := U) (S := S)).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  change (∏ s : U ⊕ Sigma S, (1 / 2 : ℝ)) =
    (∏ u : U, (1 / 2 : ℝ)) * ∏ a, ∏ s : S a, (1 / 2 : ℝ)
  rw [Fintype.prod_sum_type, Fintype.prod_sigma]

end FairSites

variable {I T Q : Type*} [Fintype I] [Fintype T] [DecidableEq T]

/-- All-block centered cancellation is combined with a genuinely normalized
product exterior. The necessity premise is an event implication, not the desired
probability or forest-integral estimate. -/
theorem centered_probe_bound (ν₀ : FiniteLaw Z) (ν : ∀ a, FiniteLaw (Ξ a))
    (w : I → (T → PairColor) → ℝ)
    (cross : (Z × (∀ a, Ξ a)) → Q → T → (I → PairColor) → Bool)
    (outer : (Z × (∀ a, Ξ a)) → (Q × T → Bool) → ℝ)
    (E : ∀ a, Ξ a → Prop)
    (hw : ∀ i, ∑ h, w i h = 0)
    (hf : ∀ o h, |outer o (historyTests (cross o) h)| ≤ 1)
    (hnecessary : ∀ o, AllEndpointPivotal (cross o) → ∀ a, E a (o.2 a)) :
    |(probeLaw ν₀ ν).expect (fun o => kernel w
        (fun h => outer o (historyTests (cross o) h)))| ≤
      (∏ i, variation (w i)) * ∏ a, probability (ν a) (E a) := by
  have hpoint (o : Z × (∀ a, Ξ a)) :
      |kernel w (fun h => outer o (historyTests (cross o) h))| ≤
        (∏ i, variation (w i)) * indicator (∀ a, E a (o.2 a)) := by
    by_cases he : ∀ a, E a (o.2 a)
    · simp only [indicator, ite_eq_left he, mul_one]
      simpa only [mul_one] using kernel_variation_bound w _ 1 (hf o)
    · have hz : kernel w (fun h => outer o (historyTests (cross o) h)) = 0 := by
        by_contra hn
        exact he (hnecessary o (pair_history_pivotal_witness w (cross o) (outer o) hw hn))
      simp [hz, indicator, he]
  calc
    _ ≤ (probeLaw ν₀ ν).expect (fun o =>
        |kernel w (fun h => outer o (historyTests (cross o) h))|) :=
      (probeLaw ν₀ ν).abs_expect_le _
    _ ≤ (probeLaw ν₀ ν).expect (fun o =>
        (∏ i, variation (w i)) * indicator (∀ a, E a (o.2 a))) :=
      (probeLaw ν₀ ν).expect_mono hpoint
    _ = _ := by
      rw [FiniteLaw.expect_const_mul]
      congr 1
      exact probability_probeLaw ν₀ ν E

/-- Insert static one-probe bounds after a finite union over witness choices.
There is no union over the assignments of other selected histories. -/
theorem centered_arm_product_bound
    {C : A → Type*} [∀ a, Fintype (C a)]
    (ν₀ : FiniteLaw Z) (ν : ∀ a, FiniteLaw (Ξ a))
    (w : I → (T → PairColor) → ℝ)
    (cross : (Z × (∀ a, Ξ a)) → Q → T → (I → PairColor) → Bool)
    (outer : (Z × (∀ a, Ξ a)) → (Q × T → Bool) → ℝ)
    (Arm : ∀ a, C a → Ξ a → Prop) (α : ∀ a, C a → ℝ)
    (hw : ∀ i, ∑ h, w i h = 0)
    (hf : ∀ o h, |outer o (historyTests (cross o) h)| ≤ 1)
    (hnecessary : ∀ o, AllEndpointPivotal (cross o) → ∀ a, ∃ c, Arm a c (o.2 a))
    (hstatic : ∀ a c, probability (ν a) (Arm a c) ≤ α a c) :
    |(probeLaw ν₀ ν).expect (fun o => kernel w
        (fun h => outer o (historyTests (cross o) h)))| ≤
      (∏ i, variation (w i)) * ∏ a, ∑ c, α a c := by
  refine (centered_probe_bound ν₀ ν w cross outer (fun a x => ∃ c, Arm a c x)
    hw hf hnecessary).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod₀
    · intro a _
      exact probability_nonneg _ _
    · intro a _
      exact (probability_exists_le (ν a) (Arm a)).trans
        (Finset.sum_le_sum (fun c _ => hstatic a c))
  · exact Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun h _ => abs_nonneg (w i h)))

/-- The centered-block arm-product estimate under the original independent
fair colors on a finite physical site set. A site bijection certifies the disjoint
probe partition; its existence and the local arm necessity are geometric inputs. -/
theorem fair_site_centered_arm_bound
    {D U : Type*} [Fintype D] [DecidableEq D] [Fintype U] [DecidableEq U]
    {S : A → Type*} [∀ a, Fintype (S a)] [∀ a, DecidableEq (S a)]
    {C : A → Type*} [∀ a, Fintype (C a)] (sites : D ≃ (U ⊕ Sigma S))
    (w : I → (T → PairColor) → ℝ)
    (cross : ((U → Bool) × (∀ a, S a → Bool)) → Q → T → (I → PairColor) → Bool)
    (outer : ((U → Bool) × (∀ a, S a → Bool)) → (Q × T → Bool) → ℝ)
    (Arm : ∀ a, C a → (S a → Bool) → Prop) (α : ∀ a, C a → ℝ)
    (hw : ∀ i, ∑ h, w i h = 0)
    (hf : ∀ o h, |outer o (historyTests (cross o) h)| ≤ 1)
    (hnecessary : ∀ o, AllEndpointPivotal (cross o) → ∀ a, ∃ c, Arm a c (o.2 a))
    (hstatic : ∀ a c, probability (fairSites (S a)) (Arm a c) ≤ α a c) :
    |(fairSites D).expect (fun ω =>
        let o := splitSites (relabelColors sites ω)
        kernel w (fun h => outer o (historyTests (cross o) h)))| ≤
      (∏ i, variation (w i)) * ∏ a, ∑ c, α a c := by
  let f : ((U → Bool) × (∀ a, S a → Bool)) → ℝ :=
    fun o => kernel w (fun h => outer o (historyTests (cross o) h))
  change |(fairSites D).expect (fun ω => f (splitSites (relabelColors sites ω)))| ≤ _
  rw [fairSites_relabel sites (fun ξ => f (splitSites ξ)), fairSites_split_expect f]
  exact centered_arm_product_bound (fairSites U) (fun a => fairSites (S a))
    w cross outer Arm α hw hf hnecessary hstatic

#print axioms probability_pi
#print axioms centered_probe_bound
#print axioms centered_arm_product_bound
#print axioms fairSites_split_expect
#print axioms fair_site_centered_arm_bound

end ExceptionalTimes.ProbeProduct
