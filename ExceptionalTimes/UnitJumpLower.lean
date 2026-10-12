import ExceptionalTimes.UnitReferenceCover
import ExceptionalTimes.DimerSingleton

/-! The actual degree-one canonical reference jump has a bulk lower
bound. The only percolation input is PublishedUnitAttachment, a narrow
ordinary static arm-attachment consequence. The matching cover, positive
density, finite-law dictionary and canonical response are proved. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.UnitJumpLower
noncomputable section
open PairSquareSewing UnitStaticAttachment UnitReferenceCover DimerJumpCalibration

def jump (phase : Bool) (e : ℝ) (he : 0<e) : ℝ :=
  canonicalJump (slot phase (sourceReferenceAt e he 0).support) (sourceReferenceAt e he 0)

def referenceJump (phase : Bool) (n : ℕ) : ℝ :=
  jump phase (IndependentAnnulusInput.mesh n) (IndependentAnnulusInput.mesh_pos n)

set_option maxHeartbeats 1200000 in
theorem canonicalJump_eq_response_sum (phase : Bool) (Q : PolygonQuad) :
    canonicalJump (slot phase Q.support) Q=
      ∑ b : anchors phase Q.support,averagedResponse .canonical Q.support Q b.val := by
  rw [canonicalJump_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hh := DimerSingleton.canonical_singleton_jump (slot phase Q.support) Q
    (slot_covers phase Q.support) b b.val (1,0) (slot_zero phase Q.support b)
      (slot_one phase Q.support b)
  refine hh.trans ?_
  apply EnvironmentVariance.FiniteLaw.expect_congr
  intro ω
  have hF : jumpTest Q=Q.jump := by
    funext η
    simp [jumpTest,EnvironmentVariance.indicator,PolygonQuad.jump]
  rw [hF]

theorem jump_nonneg (phase : Bool) (e : ℝ) (he : 0<e) : 0≤jump phase e he := by
  rw [jump,canonicalJump_eq_response_sum]
  exact Finset.sum_nonneg (fun _ _ => averagedResponse_nonneg ..)

theorem sum_embedding_le {A B : Type*} [Fintype A] [Fintype B]
    (em : A ↪ B) (f : B→ℝ) (hf : ∀ b,0≤f b) : (∑ a,f (em a))≤∑ b,f b := by
  calc
    _=∑ b∈Finset.univ.map em,f b := by rw [Finset.sum_map]
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => hf b)

theorem jump_lower_grid (B0 : ℝ) (h : PublishedUnitAttachment B0) :
    ∃ c : ℝ,0<c ∧ ∃ e0 : ℝ,0<e0 ∧
      ∀ phase : Bool,∀ e : ℝ,∀ he : 0<e,e<e0 → ∀ hsmall : 4*(B0*e)<1,
        ∀ m : ℕ,e*(m:ℝ)≤1/64 →
          c*(m:ℝ)^2*sourceArmCost e (B0*e) he (mul_pos (by linarith [h.1]) he) hsmall ≤
            jump phase e he := by
  obtain ⟨c,hc,e0,he0,hlocal⟩ := published_local_response_any_cover B0 h
  refine ⟨c,hc,e0,he0,?_⟩
  intro phase e he hee hsmall m hem
  let Q := sourceReferenceAt e he 0
  let em := gridInCover phase e he m hem
  have hpoint (i : Fin m×Fin m) :
      c*sourceArmCost e (B0*e) he (mul_pos (by linarith [h.1]) he) hsmall ≤
        averagedResponse .canonical Q.support Q (em i).val :=
    hlocal e he hee hsmall (gridAnchor phase i) (gridAnchor_bulk phase i e he hem)
      .canonical Q.support (Finset.Subset.refl _)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m×Fin m)))
    (fun i _ => hpoint i)
  have hsum' : c*(m:ℝ)^2*sourceArmCost e (B0*e) he (mul_pos (by linarith [h.1]) he) hsmall ≤
      ∑ i : Fin m×Fin m,averagedResponse .canonical Q.support Q (em i).val := by
    calc
      _=∑ _i : Fin m×Fin m,c*sourceArmCost e (B0*e) he
          (mul_pos (by linarith [h.1]) he) hsmall := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_mul]
        ring
      _≤_ := hsum
  apply hsum'.trans
  rw [jump,canonicalJump_eq_response_sum]
  exact sum_embedding_le em (fun b => averagedResponse .canonical Q.support Q b.val)
    (fun _ => averagedResponse_nonneg ..)

theorem mesh_grid_identity (n : ℕ) (hn : 6≤n) :
    IndependentAnnulusInput.mesh n*(2^(n-6):ℕ)=1/64 := by
  have hp : (2:ℝ)^n=64*(2:ℝ)^(n-6) := by
    conv_lhs => rw [show n=(n-6)+6 by omega,pow_add]
    norm_num
    ring
  unfold IndependentAnnulusInput.mesh
  push_cast
  rw [hp]
  field_simp

theorem grid_card_identity (n : ℕ) (hn : 6≤n) :
    ((2^(n-6):ℕ):ℝ)^2=(2:ℝ)^(2*n)/4096 := by
  have hp : (2:ℝ)^n=64*(2:ℝ)^(n-6) := by
    conv_lhs => rw [show n=(n-6)+6 by omega,pow_add]
    norm_num
    ring
  push_cast
  rw [mul_comm 2 n,pow_mul,hp]
  ring

/-- Literal global bulk lower bound, uniform in the two matching phases.
The harmless explicit small-mesh clauses may be absorbed into a single
eventual threshold by the downstream numerical clock argument. -/
theorem referenceJump_lower (B0 : ℝ) (h : PublishedUnitAttachment B0) :
    ∃ c : ℝ,0<c ∧ ∃ e0 : ℝ,0<e0 ∧
      ∀ phase : Bool,∀ n : ℕ,6≤n → IndependentAnnulusInput.mesh n<e0 →
        ∀ hsmall : 4*(B0*IndependentAnnulusInput.mesh n)<1,
          c*(2:ℝ)^(2*n)*sourceArmCost (IndependentAnnulusInput.mesh n)
            (B0*IndependentAnnulusInput.mesh n) (IndependentAnnulusInput.mesh_pos n)
            (mul_pos (by linarith [h.1]) (IndependentAnnulusInput.mesh_pos n)) hsmall ≤
              referenceJump phase n := by
  obtain ⟨c,hc,e0,he0,hbound⟩ := jump_lower_grid B0 h
  refine ⟨c/4096,by positivity,e0,he0,?_⟩
  intro phase n hn hne hsmall
  have hb := hbound phase (IndependentAnnulusInput.mesh n) (IndependentAnnulusInput.mesh_pos n)
    hne hsmall (2^(n-6)) (mesh_grid_identity n hn).le
  rw [grid_card_identity n hn] at hb
  change _≤jump phase _ _
  convert hb using 1
  ring

#print axioms canonicalJump_eq_response_sum
#print axioms referenceJump_lower
end
end ExceptionalTimes.UnitJumpLower
