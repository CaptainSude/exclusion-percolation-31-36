import ExceptionalTimes.CircularForestMass
import ExceptionalTimes.DyadicForestEnvelope
import ExceptionalTimes.WordProductBridge

/-! Actual dyadic box covers satisfy one common all-degree majorant,
uniform over both matching phases and both local calibration rules. -/

open Filter
open scoped Classical BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.DyadicForestMass
open PairSquareSewing CircularStaticProfile DyadicForestEnvelope
open SelectedPerturbation WordProductBridge IndependentAnnulusInput

variable {F : Type*} [Fintype F]

theorem phase_mass (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R : ℕ) (phase : Bool) {B C₄ C₃ Q c g : ℝ}
    (hstatic : PublishedCircularArmInputs B C₄ Q c g)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B) :
    ∃ A : ℝ, 0≤A ∧ ∀ᶠ n in atTop, ∀ rule : Rule, ∀ k : ℕ,
      (localScale rule n)^k * geometryDegree (value hplane T R phase B C₄ C₃ Q c g n) k ≤
        A^k * (k:ℝ)^(-(1-g/2)*k) := by
  exact CircularForestMass.eventual_profile_mass
    (fun n => UnitReferenceCover.anchors phase (sites R n))
    (fun n => (Equiv.refl (Blocks R phase n)).toEmbedding)
    (geometry hplane T R phase) hstatic hattach T.stop_pos (stop_four_lt_one T)
    (ballRadius_pos R) 0 (fun _ => T.root hplane)
    (fun n S => geometry_root hplane T R phase n S)
    (fun n S i => geometry_anchor hplane T R phase n S i)
    (fun n S => (geometry_margin hplane T R phase n S).le)
    (fun n a ha => anchor_bound R phase n a ha)

theorem uniform_mass (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R : ℕ) {B C₄ C₃ Q c g : ℝ}
    (hstatic : PublishedCircularArmInputs B C₄ Q c g)
    (hattach : UnitStaticAttachment.PublishedUnitAttachment B) :
    ∃ A : ℝ, 0≤A ∧ ∀ phase : Bool, ∀ rule : Rule, ∀ᶠ n in atTop, ∀ k : ℕ,
      (localScale rule n)^k * geometryDegree (value hplane T R phase B C₄ C₃ Q c g n) k ≤
        A^k * (k:ℝ)^(-(1-g/2)*k) := by
  obtain ⟨A₀,hA₀,h₀⟩ := phase_mass hplane T R false (C₃:=C₃) hstatic hattach
  obtain ⟨A₁,hA₁,h₁⟩ := phase_mass hplane T R true (C₃:=C₃) hstatic hattach
  refine ⟨max A₀ A₁,hA₀.trans (le_max_left _ _),?_⟩
  intro phase rule
  cases phase
  · filter_upwards [h₀] with n hn
    intro k
    exact (hn rule k).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hA₀ (le_max_left _ _) k) (Real.rpow_nonneg (Nat.cast_nonneg k) _))
  · filter_upwards [h₁] with n hn
    intro k
    exact (hn rule k).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hA₁ (le_max_right _ _) k) (Real.rpow_nonneg (Nat.cast_nonneg k) _))

#print axioms uniform_mass
end ExceptionalTimes.DyadicForestMass
