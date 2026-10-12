import ExceptionalTimes.EnvironmentVariance

/-! Association controls arbitrary finite binary words by coordinate
covariances. In particular the words need not be increasing. This is
an algebraic lemma; no continuum mixing theorem is assumed here. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.FiniteWordMixing

open EnvironmentVariance

noncomputable def bit (b : Bool) : ℝ := if b then 1 else 0

theorem bit_nonneg (b : Bool) : 0≤bit b := by cases b <;> norm_num [bit]

theorem bit_mono : Monotone bit := by
  intro a b hab
  cases a <;> cases b <;> simp_all [bit]
  exact False.elim (Bool.false_lt_true.not_ge hab)

noncomputable def count {I : Type*} [Fintype I] (x : I→Bool) : ℝ := ∑ i,bit (x i)

theorem count_nonneg {I : Type*} [Fintype I] (x : I→Bool) : 0≤count x :=
  Finset.sum_nonneg (fun i _ => bit_nonneg (x i))

theorem count_gap {I : Type*} [Fintype I] {x y : I→Bool}
    (hxy : x≤y) (hne : x≠y) : count x+1≤count y := by
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hne
  have hgap : bit (x j)+1≤bit (y j) := by
    have hle := hxy j
    cases hx : x j <;> cases hy : y j <;> simp_all [bit]
    exact False.elim (Bool.false_lt_true.not_ge hle)
  calc
    count x+1 = ∑ i, (bit (x i)+if i=j then (1:ℝ) else 0) := by
      simp [count,Finset.sum_add_distrib]
    _ ≤ ∑ i,bit (y i) := Finset.sum_le_sum (fun i _ => by
      by_cases hi : i=j
      · subst i; simpa using hgap
      · simpa [hi] using bit_mono (hxy i))
    _ = count y := rfl

theorem compensated_plus_mono {I : Type*} [Fintype I] (F : (I→Bool)→ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) : Monotone (fun x => count x+F x) := by
  intro x y hxy
  by_cases he : x=y
  · subst y; rfl
  · have hg := count_gap hxy he
    linarith [(hF x).2,(hF y).1]

theorem compensated_minus_mono {I : Type*} [Fintype I] (F : (I→Bool)→ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) : Monotone (fun x => count x-F x+1) := by
  intro x y hxy
  by_cases he : x=y
  · subst y; rfl
  · have hg := count_gap hxy he
    linarith [(hF x).1,(hF y).2]

noncomputable def covariance {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (f g : Ω→ℝ) : ℝ := μ.expect (fun ω => f ω*g ω)-μ.expect f*μ.expect g

variable {Ω : Type*} [Fintype Ω]

theorem covariance_add_left (μ : FiniteLaw Ω) (f g h : Ω→ℝ) :
    covariance μ (fun ω => f ω+g ω) h = covariance μ f h+covariance μ g h := by
  simp only [covariance,add_mul,μ.expect_add]
  ring

theorem covariance_sub_left (μ : FiniteLaw Ω) (f g h : Ω→ℝ) :
    covariance μ (fun ω => f ω-g ω) h = covariance μ f h-covariance μ g h := by
  simp only [covariance,sub_mul,μ.expect_sub]
  ring

theorem covariance_add_right (μ : FiniteLaw Ω) (f g h : Ω→ℝ) :
    covariance μ f (fun ω => g ω+h ω) = covariance μ f g+covariance μ f h := by
  simp only [covariance,mul_add,μ.expect_add]
  ring

theorem covariance_sub_right (μ : FiniteLaw Ω) (f g h : Ω→ℝ) :
    covariance μ f (fun ω => g ω-h ω) = covariance μ f g-covariance μ f h := by
  simp only [covariance,mul_sub,μ.expect_sub]
  ring

@[simp] theorem covariance_const_left (μ : FiniteLaw Ω) (c : ℝ) (f : Ω→ℝ) :
    covariance μ (fun _ => c) f=0 := by
  simp [covariance,μ.expect_const_mul]

@[simp] theorem covariance_const_right (μ : FiniteLaw Ω) (f : Ω→ℝ) (c : ℝ) :
    covariance μ f (fun _ => c)=0 := by
  simp [covariance,μ.expect_mul_const]

/-- Cross-association suffices: no monotonicity is imposed on F or G. -/
theorem word_covariance_le_count_covariance {I J : Type*} [Fintype I] [Fintype J]
    (μ : FiniteLaw Ω) (X : Ω→I→Bool) (Y : Ω→J→Bool)
    (hassoc : ∀ (f : (I→Bool)→ℝ) (g : (J→Bool)→ℝ),
      (∀ x,0≤f x) → (∀ y,0≤g y) → Monotone f → Monotone g →
      0≤covariance μ (fun ω => f (X ω)) (fun ω => g (Y ω)))
    (F : (I→Bool)→ℝ) (G : (J→Bool)→ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) (hG : ∀ y,0≤G y ∧ G y≤1) :
    |covariance μ (fun ω => F (X ω)) (fun ω => G (Y ω))| ≤
      covariance μ (fun ω => count (X ω)) (fun ω => count (Y ω)) := by
  have hFp := compensated_plus_mono F hF
  have hFm := compensated_minus_mono F hF
  have hGp := compensated_plus_mono G hG
  have hGm := compensated_minus_mono G hG
  have hFp0 (x) : 0≤count x+F x := add_nonneg (count_nonneg x) (hF x).1
  have hFm0 (x) : 0≤count x-F x+1 := by linarith [count_nonneg x,(hF x).2]
  have hGp0 (y) : 0≤count y+G y := add_nonneg (count_nonneg y) (hG y).1
  have hGm0 (y) : 0≤count y-G y+1 := by linarith [count_nonneg y,(hG y).2]
  have hpp := hassoc _ _ hFp0 hGp0 hFp hGp
  have hpm := hassoc _ _ hFp0 hGm0 hFp hGm
  have hmp := hassoc _ _ hFm0 hGp0 hFm hGp
  have hmm := hassoc _ _ hFm0 hGm0 hFm hGm
  simp only [covariance_add_left,covariance_sub_left,covariance_add_right,
    covariance_sub_right,covariance_const_left,covariance_const_right,add_zero] at hpp hpm hmp hmm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem expect_sum {I : Type*} [Fintype I] (μ : FiniteLaw Ω) (f : I→Ω→ℝ) :
    μ.expect (fun ω => ∑ i,f i ω)=∑ i,μ.expect (f i) := by
  simp only [FiniteLaw.expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem covariance_sum_left {I : Type*} [Fintype I] (μ : FiniteLaw Ω)
    (f : I→Ω→ℝ) (g : Ω→ℝ) :
    covariance μ (fun ω => ∑ i,f i ω) g=∑ i,covariance μ (f i) g := by
  simp only [covariance,Finset.sum_mul,expect_sum,Finset.sum_sub_distrib]

theorem covariance_sum_right {I : Type*} [Fintype I] (μ : FiniteLaw Ω)
    (f : Ω→ℝ) (g : I→Ω→ℝ) :
    covariance μ f (fun ω => ∑ i,g i ω)=∑ i,covariance μ f (g i) := by
  simp only [covariance,Finset.mul_sum,expect_sum,Finset.sum_sub_distrib]

theorem count_covariance_eq_sum {I J : Type*} [Fintype I] [Fintype J]
    (μ : FiniteLaw Ω) (X : Ω→I→Bool) (Y : Ω→J→Bool) :
    covariance μ (fun ω => count (X ω)) (fun ω => count (Y ω)) =
      ∑ i,∑ j,covariance μ (fun ω => bit (X ω i)) (fun ω => bit (Y ω j)) := by
  simp only [count,covariance_sum_left,covariance_sum_right]
  exact Finset.sum_comm

#print axioms word_covariance_le_count_covariance
#print axioms count_covariance_eq_sum

theorem word_covariance_le_sum {I J : Type*} [Fintype I] [Fintype J]
    (μ : FiniteLaw Ω) (X : Ω→I→Bool) (Y : Ω→J→Bool)
    (hassoc : ∀ (f : (I→Bool)→ℝ) (g : (J→Bool)→ℝ),
      (∀ x,0≤f x) → (∀ y,0≤g y) → Monotone f → Monotone g →
      0≤covariance μ (fun ω => f (X ω)) (fun ω => g (Y ω)))
    (F : (I→Bool)→ℝ) (G : (J→Bool)→ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) (hG : ∀ y,0≤G y ∧ G y≤1) :
    |covariance μ (fun ω => F (X ω)) (fun ω => G (Y ω))| ≤
      ∑ i,∑ j,covariance μ (fun ω => bit (X ω i)) (fun ω => bit (Y ω j)) :=
  (word_covariance_le_count_covariance μ X Y hassoc F G hF hG).trans_eq
    (count_covariance_eq_sum μ X Y)

#print axioms word_covariance_le_sum

end ExceptionalTimes.FiniteWordMixing
