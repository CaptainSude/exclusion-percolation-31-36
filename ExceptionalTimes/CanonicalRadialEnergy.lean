import ExceptionalTimes.ConcreteCanonicalDriver
import ExceptionalTimes.RadialEnergy

/-! The literal canonical finite-law radial power bound implies the exact
extended matching energy used by the main driver. The radial power bound
is a NEW hypothesis, not a published input. The integration, endpoint,
normalization and uniformity conversions are proved here. -/

open MeasureTheory Set
open scoped ENNReal Classical

namespace ExceptionalTimes.CanonicalRadialEnergy

open FiniteMatchingExhaustion FiniteClockBridge FiniteMatchingClosure
open ConcreteCanonicalDriver

theorem canonicalEnergy_le_of_power_bound {k : ℕ} (slot : Fin k×Fin 2 ↪ Site)
    (E : Configuration→Prop) {γ p C a : ℝ} (hC : 0≤C)
    (hbound : ∀ t∈Ioo (0 : ℝ) 1,
      ManyDimerLaw.manyProbability (fun _ => DimerLaw.refreshProbability t)
        (fun η => E (decode slot η)) ≤ C*a^2*t^(-p))
    (hexponent : γ+p<1) :
    canonicalEnergy slot E γ ≤ ENNReal.ofReal (C*a^2/(1-(γ+p))) := by
  have hint : IntegrableOn (fun t : ℝ => C*a^2*t^(-(γ+p))) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ)<1)).mpr (by linarith)).const_mul _
  have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 1),
      0≤C*a^2*t^(-(γ+p)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact mul_nonneg (mul_nonneg hC (sq_nonneg a)) (Real.rpow_nonneg ht.1.le _)
  unfold canonicalEnergy
  rw [← restrict_Ioo_eq_restrict_Ioc]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioo 0 1, ENNReal.ofReal (C*a^2*t^(-(γ+p))) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      rw [frostmanKernel_off_diagonal γ (ne_of_lt ht.1)]
      have hd : dist (0 : ℝ) t=t := by simp [Real.dist_eq,abs_of_pos ht.1]
      rw [hd,← ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ t^(-γ)*(C*a^2*t^(-p)) := mul_le_mul_of_nonneg_left (hbound t ht)
          (Real.rpow_nonneg ht.1.le _)
        _ = _ := by
          rw [show -(γ+p)=-γ + -p by ring,Real.rpow_add ht.1]
          ring
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
        integral_const_mul,power_integral_unit hexponent]
      congr 1
      ring

/-- The exact NEW radial probability estimate, uniformly over observation
radii and every enumeration of the actual matching closure. -/
def NewCanonicalRadialPower (z : Site) : Prop :=
  ∀ δ : ℝ,0<δ → ∃ C : ℝ,0≤C ∧
    ∀ R k (slot : Fin k×Fin 2 ↪ Site),
      (∀ x,x∈closure (PeriodicMatching.partner z) (latticeBox (R+1)) ↔ ∃ b,slot b=x) →
      (∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
      ∀ t∈Ioo (0 : ℝ) 1,
        ManyDimerLaw.manyProbability (fun _ => DimerLaw.refreshProbability t)
          (fun η => OneArm (decode slot η) (0,0) R) ≤
            C*(finiteFairOneArm R).toReal^2*t^(-(5/36+δ))

theorem canonical_energy_of_radial_power (z : Site) (hpower : NewCanonicalRadialPower z) :
    CanonicalOneArmEnergyBound z (0,0) finiteFairOneArm := by
  intro γ _ hγ
  obtain ⟨δ,hδ,hexponent⟩ := exists_radial_exponent_loss hγ
  obtain ⟨C,hC,hbound⟩ := hpower δ hδ
  let K : ℝ := C/(1-(γ+(5/36+δ)))
  have hK : 0≤K := div_nonneg hC (by linarith)
  refine ⟨K+1,by linarith,?_⟩
  intro R k slot hcover hpair
  have h := canonicalEnergy_le_of_power_bound slot (fun η => OneArm η (0,0) R)
    hC (hbound R k slot hcover hpair) hexponent
  have hα : finiteFairOneArm R≠⊤ := ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal (K*(finiteFairOneArm R).toReal^2) := by
      convert h using 2
      dsimp only [K]
      ring
    _ = ENNReal.ofReal K*(finiteFairOneArm R)^2 := by
      rw [ENNReal.ofReal_mul hK,ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hα]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith : K≤K+1)) le_rfl

#print axioms canonicalEnergy_le_of_power_bound
#print axioms canonical_energy_of_radial_power

end ExceptionalTimes.CanonicalRadialEnergy
