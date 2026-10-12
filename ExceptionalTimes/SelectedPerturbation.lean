import ExceptionalTimes.SelectedKernelLaw
import ExceptionalTimes.PerturbationControl
import ExceptionalTimes.ExpansionLimit

/-! A geometry bound for arbitrary centered selected insertions controls
semigroup remainders before summing the update degrees. No probabilistic
estimate is introduced by these finite algebraic lemmas. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.SelectedPerturbation
noncomputable section

open EnvironmentVariance CenteredBlocks BlockExpansion SelectedKernelLaw
open ExpansionLimit

variable {B H : Type*} [Fintype B] [Fintype H]
local instance : DecidableEq B := fun a b => Classical.propDecidable (a=b)

theorem kernel_expect {O I X : Type*} [Fintype O] [Fintype I] [Fintype X]
    (μ : FiniteLaw O) (w : I→X→ℝ) (f : O→(I→X)→ℝ) :
    kernel w (fun z => μ.expect (fun o => f o z))=
      μ.expect (fun o => kernel w (f o)) := by
  unfold kernel FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro z _
  ring

def exteriorTest (μ : B→FiniteLaw H) (S : Finset B) (f : (B→H)→ℝ)
    (z : S→H) : ℝ :=
  (FiniteLaw.pi (fun b : {b // b∉S} => μ b)).expect (fun o => f (join S z o))

theorem selected_integrated (μ : B→FiniteLaw H) (u : B→H→ℝ)
    (S : Finset B) (f : (B→H)→ℝ) :
    selectedKernel (fun b => (μ b).weight) u S f=
      kernel (fun b : S => u b) (exteriorTest μ S f) := by
  rw [selectedKernel_exterior]
  exact (kernel_expect _ _ (fun o z => f (join S z o))).symm

def liftWeights (S : Finset B) (w : S→H→ℝ) (b : B) : H→ℝ :=
  if hb : b∈S then w ⟨b,hb⟩ else fun _ => 0

omit [Fintype B] [Fintype H] in
theorem liftWeights_inside (S : Finset B) (w : S→H→ℝ) (b : S) :
    liftWeights S w b=w b := by simp [liftWeights,b.property]

omit [Fintype B] in
theorem liftWeights_centered (S : Finset B) (w : S→H→ℝ)
    (hw : ∀ b,∑ h,w b h=0) : ∀ b,∑ h,liftWeights S w b h=0 := by
  intro b
  by_cases hb : b∈S
  · simpa only [liftWeights,dite_eq_left hb] using hw ⟨b,hb⟩
  · simp [liftWeights,hb]

omit [Fintype B] in
theorem product_lift_variation (S : Finset B) (w : S→H→ℝ) :
    (∏ b∈S,variation (liftWeights S w b))=∏ b : S,variation (w b) := by
  rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
  exact Finset.prod_congr rfl (fun b _ => congrArg variation (liftWeights_inside S w b))

/-- The selected geometry bound is an explicit input here; callers prove
it from the actual forest estimate, rather than treating it as literature. -/
def GeometryBound (μ : B→FiniteLaw H) (f : (B→H)→ℝ) (G : Finset B→ℝ) : Prop :=
  ∀ S : Finset B,∀ w : B→H→ℝ,(∀ b,∑ h,w b h=0) →
    |selectedKernel (fun b => (μ b).weight) w S f|≤G S*∏ b∈S,variation (w b)

theorem exterior_bound (μ : B→FiniteLaw H) (f : (B→H)→ℝ) (G : Finset B→ℝ)
    (hG : GeometryBound μ f G) (S : Finset B) (w : S→H→ℝ)
    (hw : ∀ b,∑ h,w b h=0) :
    |kernel w (exteriorTest μ S f)|≤G S*∏ b,variation (w b) := by
  have h := hG S (liftWeights S w) (liftWeights_centered S w hw)
  rw [selected_integrated,product_lift_variation] at h
  simpa only [liftWeights_inside] using h

theorem selected_remainder (μ : B→FiniteLaw H) (f : (B→H)→ℝ) (G : Finset B→ℝ)
    (hG : GeometryBound μ f G) (hG0 : ∀ S,0≤G S)
    (u r : B→H→ℝ) (hu : ∀ b,∑ h,u b h=0) (hr : ∀ b,∑ h,r b h=0)
    {A R : ℝ} (hA : 0≤A) (hR : 0≤R)
    (hvu : ∀ b,variation (u b)≤A) (hvr : ∀ b,variation (r b)≤R) (S : Finset B) :
    |selectedKernel (fun b => (μ b).weight) (fun b h => u b h+r b h) S f-
      selectedKernel (fun b => (μ b).weight) u S f|≤
        G S*(R*S.card*(A+R)^(S.card-1)) := by
  rw [selected_integrated,selected_integrated]
  have h := PerturbationControl.centered_product_remainder_bound_linear
    (fun b : S => u b) (fun b : S => r b) (exteriorTest μ S f)
    (fun b => hu b) (fun b => hr b) hA hR (hG0 S)
    (fun b => hvu b) (fun b => hvr b)
    (fun w hw => exterior_bound μ f G hG S w hw)
  simpa only [Fintype.card_coe] using h

def geometryDegree (G : Finset B→ℝ) (k : ℕ) : ℝ :=
  ∑ S∈(Finset.univ : Finset (Finset B)).filter (fun S => S.card=k),G S

theorem coefficient_bound (μ : B→FiniteLaw H) (f : (B→H)→ℝ) (G : Finset B→ℝ)
    (hG : GeometryBound μ f G) (hG0 : ∀ S,0≤G S)
    (u : B→H→ℝ) (hu : ∀ b,∑ h,u b h=0)
    {V : ℝ} (_hV : 0≤V) (hvu : ∀ b,variation (u b)≤V) (k : ℕ) :
    |coefficient (fun b => (μ b).weight) u f k|≤geometryDegree G k*V^k := by
  unfold coefficient geometryDegree
  rw [Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  have he : S.card=k := (Finset.mem_filter.mp hS).2
  apply (hG S u hu).trans
  apply mul_le_mul_of_nonneg_left ?_ (hG0 S)
  calc
    _ ≤ ∏ _b∈S,V := Finset.prod_le_prod₀
      (fun b _ => Finset.sum_nonneg (fun h _ => abs_nonneg (u b h))) (fun b _ => hvu b)
    _ = V^k := by simp [he]

theorem coefficient_remainder (μ : B→FiniteLaw H) (f : (B→H)→ℝ) (G : Finset B→ℝ)
    (hG : GeometryBound μ f G) (hG0 : ∀ S,0≤G S)
    (u r : B→H→ℝ) (hu : ∀ b,∑ h,u b h=0) (hr : ∀ b,∑ h,r b h=0)
    {A R : ℝ} (hA : 0≤A) (hR : 0≤R)
    (hvu : ∀ b,variation (u b)≤A) (hvr : ∀ b,variation (r b)≤R) (k : ℕ) :
    |coefficient (fun b => (μ b).weight) (fun b h => u b h+r b h) f k-
      coefficient (fun b => (μ b).weight) u f k|≤
        geometryDegree G k*(R*k*(A+R)^(k-1)) := by
  unfold coefficient geometryDegree
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  have he : S.card=k := (Finset.mem_filter.mp hS).2
  simpa only [he] using selected_remainder μ f G hG hG0 u r hu hr hA hR hvu hvr S

#print axioms coefficient_remainder
end
end ExceptionalTimes.SelectedPerturbation

