import ExceptionalTimes.BlockExpansion
import ExceptionalTimes.CanonicalSpatialProduct

/-! The selected coefficient of the exact product expansion is an
expectation of literal selected-coordinate overwrites under the original
normalized product law. No independence premise is needed. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.SelectedKernelLaw

open EnvironmentVariance CenteredBlocks BlockExpansion

variable {B H : Type*} [Fintype B] [Fintype H]

noncomputable local instance : DecidableEq B := Classical.decEq _

noncomputable def join (S : Finset B) (z : S → H) (o : {b // b ∉ S} → H) : B → H :=
  (Equiv.piEquivPiSubtypeProd (fun b => b ∈ S) (fun _ => H)).symm (z,o)

noncomputable def overwrite (S : Finset B) (o : B → H) (z : S → H) : B → H :=
  join S z (fun b => o b.val)

omit [Fintype B] [Fintype H] in
theorem join_inside (S : Finset B) (z : S → H) (o : {b // b ∉ S} → H) (b : S) :
    join S z o b.val=z b := by simp [join,Equiv.piEquivPiSubtypeProd,b.property]

omit [Fintype B] [Fintype H] in
theorem join_outside (S : Finset B) (z : S → H) (o : {b // b ∉ S} → H) (b : {b // b ∉ S}) :
    join S z o b.val=o b := by simp [join,Equiv.piEquivPiSubtypeProd,b.property]

theorem pi_subset_expect (μ : B → FiniteLaw H) (S : Finset B) (F : (B → H) → ℝ) :
    (FiniteLaw.pi μ).expect F =
      (FiniteLaw.pi (fun b : S => μ b.val)).expect (fun z =>
        (FiniteLaw.pi (fun b : {b // b ∉ S} => μ b.val)).expect (fun o => F (join S z o))) := by
  unfold FiniteLaw.expect
  rw [← (Equiv.piEquivPiSubtypeProd (fun b => b ∈ S) (fun _ : B => H)).symm.sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext x; simp)
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext x; simp)
  intro o _
  change (∏ b, (μ b).weight (join S z o b))*F (join S z o)=_
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun b => b ∈ S)]
  simp only [join_inside,join_outside,FiniteLaw.pi]
  simp only [mul_comm,mul_left_comm]
  apply congrArg₂ (fun x y : ℝ => F (join S z o)*(x*y))
  all_goals
    apply Finset.prod_congr (by ext b; simp)
    intro b _
    rfl

theorem selectedKernel_exterior (μ : B → FiniteLaw H) (u : B → H → ℝ)
    (S : Finset B) (F : (B → H) → ℝ) :
    selectedKernel (fun b => (μ b).weight) u S F =
      (FiniteLaw.pi (fun b : {b // b ∉ S} => μ b.val)).expect
        (fun o => kernel (fun b : S => u b.val) (fun z => F (join S z o))) := by
  unfold selectedKernel FiniteLaw.expect kernel
  rw [← (Equiv.piEquivPiSubtypeProd (fun b => b ∈ S) (fun _ : B => H)).symm.sum_comp,
    Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr (by ext x; simp)
  intro o _
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext x; simp)
  intro z _
  change ((∏ b ∈ S, u b (join S z o b))*
    (∏ b ∈ Sᶜ, (μ b).weight (join S z o b)))*F (join S z o)=_
  rw [Finset.prod_subtype S (fun _ => Iff.rfl),
    Finset.prod_subtype Sᶜ (fun b => Finset.mem_compl)]
  simp only [join_inside,join_outside,FiniteLaw.pi]
  ring

/-- The original selected coordinates integrate to one because the
overwrite discards them; the remaining exterior has its actual product law. -/
theorem selectedKernel_as_overwrite (μ : B → FiniteLaw H) (u : B → H → ℝ)
    (S : Finset B) (F : (B → H) → ℝ) :
    selectedKernel (fun b => (μ b).weight) u S F =
      (FiniteLaw.pi μ).expect (fun o =>
        kernel (fun b : S => u b.val) (fun z => F (overwrite S o z))) := by
  rw [pi_subset_expect μ S,selectedKernel_exterior]
  have hov (z y : S → H) (o : {b // b ∉ S} → H) :
      overwrite S (join S y o) z=join S z o := by
    unfold overwrite
    congr 1
    funext b
    exact join_outside S y o b
  simp only [hov,FiniteLaw.expect_const]

/-- The exterior law here is exactly ManyDimerLaw.manyLaw, and the
coefficient is exactly BlockExpansion.selectedKernel on joint histories. -/
theorem canonical_selected_coefficient (p : B → ℝ)
    (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (u : B → (DimerLaw.Color × DimerLaw.Color) → ℝ) (S : Finset B)
    (F : ((B → DimerLaw.Color) × (B → DimerLaw.Color)) → ℝ) :
    selectedKernel (fun b h => DimerLaw.twoTimeWeight (p b) h.1 h.2) u S
      (fun h => F (CanonicalSpatialProduct.pairCoordinates.symm h)) =
      (ManyDimerLaw.manyLaw p hp0 hp1).expect (fun o =>
        kernel (fun b : S => u b.val) (fun z => F
          (CanonicalSpatialProduct.pairCoordinates.symm
            (overwrite S (CanonicalSpatialProduct.pairCoordinates o) z)))) := by
  rw [CanonicalSpatialProduct.manyLaw_pi]
  simp only [Equiv.apply_symm_apply]
  exact selectedKernel_as_overwrite (fun b => DimerLaw.jointLaw (p b) (hp0 b) (hp1 b)) u S _

#print axioms canonical_selected_coefficient

#print axioms selectedKernel_as_overwrite

end ExceptionalTimes.SelectedKernelLaw
