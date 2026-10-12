import ExceptionalTimes.FiniteWordMixing
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-! The literal two-time independent site-refresh law is associated.
This is proved from the four weights and mathlib's FKG theorem, not
imported as a continuum mixing assertion. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.IndependentJointAssociation

open EnvironmentVariance FiniteWordMixing

noncomputable def pairWeight (p : ℝ) (a : Bool×Bool) : ℝ :=
  if a.1=a.2 then (2-p)/4 else p/4

theorem pairWeight_nonneg {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1) (a : Bool×Bool) :
    0≤pairWeight p a := by
  unfold pairWeight
  split_ifs <;> linarith

theorem pairWeight_total (p : ℝ) : ∑ a : Bool×Bool,pairWeight p a=1 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,pairWeight]
  norm_num
  ring

noncomputable def pairLaw (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) : FiniteLaw (Bool×Bool) :=
  ⟨pairWeight p,pairWeight_nonneg hp0 hp1,pairWeight_total p⟩

theorem pairWeight_lattice {p : ℝ} (_hp0 : 0≤p) (hp1 : p≤1)
    (a b : Bool×Bool) :
    pairWeight p a*pairWeight p b≤pairWeight p (a⊓b)*pairWeight p (a⊔b) := by
  rcases a with ⟨a₀,a₁⟩
  rcases b with ⟨b₀,b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    norm_num [pairWeight,Prod.inf_def,Prod.sup_def] <;> nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def jointLaw (p : V→ℝ) (hp0 : ∀ v,0≤p v) (hp1 : ∀ v,p v≤1) :
    FiniteLaw (V→Bool×Bool) := FiniteLaw.pi (fun v => pairLaw (p v) (hp0 v) (hp1 v))

theorem jointLaw_lattice (p : V→ℝ) (hp0 : ∀ v,0≤p v) (hp1 : ∀ v,p v≤1)
    (a b : V→Bool×Bool) :
    (jointLaw p hp0 hp1).weight a*(jointLaw p hp0 hp1).weight b≤
      (jointLaw p hp0 hp1).weight (a⊓b)*(jointLaw p hp0 hp1).weight (a⊔b) := by
  change (∏ v,pairWeight (p v) (a v))*(∏ v,pairWeight (p v) (b v))≤
    (∏ v,pairWeight (p v) (a v⊓b v))*(∏ v,pairWeight (p v) (a v⊔b v))
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀
    (fun v _ => mul_nonneg (pairWeight_nonneg (hp0 v) (hp1 v) _) (pairWeight_nonneg (hp0 v) (hp1 v) _))
    (fun v _ => pairWeight_lattice (hp0 v) (hp1 v) _ _)

theorem joint_association (p : V→ℝ) (hp0 : ∀ v,0≤p v) (hp1 : ∀ v,p v≤1)
    (f g : (V→Bool×Bool)→ℝ) (hf0 : ∀ a,0≤f a) (hg0 : ∀ a,0≤g a)
    (hf : Monotone f) (hg : Monotone g) :
    0≤covariance (jointLaw p hp0 hp1) f g := by
  let μ := jointLaw p hp0 hp1
  have H := fkg f g μ.weight μ.nonneg hf0 hg0 hf hg (jointLaw_lattice p hp0 hp1)
  rw [μ.total,one_mul] at H
  exact sub_nonneg.mpr H

def left (ω : V→Bool×Bool) : V→Bool := fun v => (ω v).1
def right (ω : V→Bool×Bool) : V→Bool := fun v => (ω v).2

omit [Fintype V] [DecidableEq V] in
theorem left_mono : Monotone (left (V := V)) := fun _ _ h v => (h v).1
omit [Fintype V] [DecidableEq V] in
theorem right_mono : Monotone (right (V := V)) := fun _ _ h v => (h v).2

/-- Every bounded binary word of finitely many increasing observations
has covariance controlled by the sum of their crossing covariances. -/
theorem independent_word_covariance_le_sum {I J : Type*} [Fintype I] [Fintype J]
    (p : V→ℝ) (hp0 : ∀ v,0≤p v) (hp1 : ∀ v,p v≤1)
    (X : (V→Bool)→I→Bool) (Y : (V→Bool)→J→Bool)
    (hX : Monotone X) (hY : Monotone Y)
    (F : (I→Bool)→ℝ) (G : (J→Bool)→ℝ)
    (hF : ∀ x,0≤F x ∧ F x≤1) (hG : ∀ y,0≤G y ∧ G y≤1) :
    |covariance (jointLaw p hp0 hp1)
      (fun ω => F (X (left ω))) (fun ω => G (Y (right ω)))|≤
    ∑ i,∑ j,covariance (jointLaw p hp0 hp1)
      (fun ω => bit (X (left ω) i)) (fun ω => bit (Y (right ω) j)) := by
  apply word_covariance_le_sum _ _ _ ?_ F G hF hG
  intro f g hf0 hg0 hf hg
  exact joint_association p hp0 hp1 _ _ (fun ω => hf0 _) (fun ω => hg0 _)
    (hf.comp (hX.comp left_mono)) (hg.comp (hY.comp right_mono))

#print axioms independent_word_covariance_le_sum

end ExceptionalTimes.IndependentJointAssociation
