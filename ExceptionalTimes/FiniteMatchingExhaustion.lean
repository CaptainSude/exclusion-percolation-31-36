import ExceptionalTimes.FiniteEdgeEnumeration

/-! Reduction from arbitrary monotone finite edge exhaustions to the literal
canonical matching energy. The canonical estimate is displayed as a hypothesis;
this module does not claim that estimate as a published input. -/

open MeasureTheory Set Filter
open scoped ENNReal Classical

namespace ExceptionalTimes.FiniteMatchingExhaustion

open FiniteClockBridge FiniteMatchingClosure FiniteEdgeEnumeration FiniteMatchingComparison

noncomputable def canonicalEnergy {k : ℕ} (slot : Fin k × Fin 2 ↪ Site)
    (E : Configuration → Prop) (γ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t *
    ENNReal.ofReal (ManyDimerLaw.manyProbability (fun _ => DimerLaw.refreshProbability t)
      (fun η => E (decode slot η)))

/-- Explicit remaining analytic target on the elementary finite product law.
No published theorem is asserted to supply this bound. -/
def CanonicalOneArmEnergyBound (z v : Site) (α : ℕ → ℝ≥0∞) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 31 / 36 → ∃ B : ℝ, 0 < B ∧
    ∀ R k (slot : Fin k × Fin 2 ↪ Site),
      (∀ x, x ∈ closure (PeriodicMatching.partner z) (latticeBox (R + 1)) ↔
        ∃ b, slot b = x) →
      (∀ b, slot (b, 1) = PeriodicMatching.partner z (slot (b, 0))) →
      canonicalEnergy slot (fun η => OneArm η v R) γ ≤ ENNReal.ofReal B * (α R) ^ 2

theorem finite_supported_time_aemeasurable
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (hr : ∀ e, 0 ≤ rate e)
    (F : Finset (Sym2 Site)) (A : Finset Site) (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ)) (γ : ℝ) :
    AEMeasurable (fun t => frostmanKernel γ 0 t *
      P.truncatedPairedCylinderProbability F E t) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  let V := vertices F ∪ A
  have hFV : vertices F ⊆ V := Finset.subset_union_left
  have hAV : A ⊆ V := Finset.subset_union_right
  have H := FiniteClockEnergy.truncated_time_aemeasurable V P (enumerate F V hFV)
    (enumerate_injective F V hFV) (fun _ => hr _)
    (fun η => E (extendColor V η)) γ
  rw [enumerate_retainedEdges] at H
  have heq : (fun t => frostmanKernel γ 0 t * P.truncatedPairedCylinderProbability F E t) =
      (fun t => frostmanKernel γ 0 t * P.truncatedPairedCylinderProbability F
        (fun η => E (extendColor V (restrictColor V η))) t) := by
    funext t
    congr 1
    unfold PoissonGraphicalRealization.truncatedPairedCylinderProbability
    congr 1
    ext ω
    exact and_congr (frame_event_iff A V hAV E hlocal _) (frame_event_iff A V hAV E hlocal _)
  rwa [heq]

theorem finite_energy_le_canonical_bound
    {Ξ Ψ : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ψ]
    {μ : Measure Ξ} {ν : Measure Ψ} {rate slowRate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (Q : PoissonGraphicalRealization ν slowRate)
    (p : Site → Site) (hp : Function.Involutive p) (hfixed : ∀ x, p x ≠ x)
    (hslow : ∀ x, slowRate s(x, p x) = 1 / 2) (hr : ∀ e, 0 ≤ rate e)
    (A : Finset Site) (F : Finset (Sym2 Site)) (hsub : closureEdges p A ⊆ F)
    (hdom : ∀ x ∈ closure p A, 1 / 2 ≤ rate s(x, p x))
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {B : ℝ≥0∞}
    (hcanonical : ∀ k (slot : Fin k × Fin 2 ↪ Site),
      (∀ x, x ∈ closure p A ↔ ∃ b, slot b = x) →
      (∀ b, slot (b, 1) = p (slot (b, 0))) → canonicalEnergy slot E γ ≤ B) :
    P.truncatedCorrelationEnergy F E γ (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (Real.exp 1 + 1) * B := by
  let V := vertices F ∪ closure p A
  have hFV : vertices F ⊆ V := Finset.subset_union_left
  have hAV : closure p A ⊆ V := Finset.subset_union_right
  obtain ⟨k, slot, hcover, hpair, H⟩ := actual_energy_le_matching_law P Q p hp hfixed hslow
    A V hAV (enumerate F V hFV) (enumerate_injective F V hFV) (fun _ => hr _)
    (by rwa [enumerate_retainedEdges]) hdom E hlocal
  have Hγ := H γ hγ0 hγ1
  rw [enumerate_retainedEdges] at Hγ
  exact Hγ.trans (mul_le_mul' le_rfl (hcanonical k slot hcover hpair))

theorem eventually_energy_le_canonical_bound
    {Ξ Ψ : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ψ]
    {μ : Measure Ξ} {ν : Measure Ψ} {rate slowRate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (Q : PoissonGraphicalRealization ν slowRate)
    (p : Site → Site) (hp : Function.Involutive p) (hfixed : ∀ x, p x ≠ x)
    (hslow : ∀ x, slowRate s(x, p x) = 1 / 2) (hr : ∀ e, 0 ≤ rate e)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (A : Finset Site) (hdom : ∀ x ∈ closure p A, 1 / 2 ≤ rate s(x, p x))
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {B : ℝ≥0∞}
    (hcanonical : ∀ k (slot : Fin k × Fin 2 ↪ Site),
      (∀ x, x ∈ closure p A ↔ ∃ b, slot b = x) →
      (∀ b, slot (b, 1) = p (slot (b, 0))) → canonicalEnergy slot E γ ≤ B) :
    ∀ᶠ n in atTop,
      P.truncatedCorrelationEnergy (F n) E γ (volume.restrict (Ioc (0 : ℝ) 1)) ≤
        ENNReal.ofReal (Real.exp 1 + 1) * B := by
  obtain ⟨N, hN⟩ := ClockField.finite_subset_exhaustion F hmono hex (closureEdges p A)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact finite_energy_le_canonical_bound P Q p hp hfixed hslow hr A (F n) (hN n hn)
    hdom E hlocal hγ0 hγ1 hcanonical

theorem finite_oneArm_energy_of_canonical_matching
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (z : Site) (hz : z ≠ (0, 0))
    (hhalf : ∀ x, rate s(x, PeriodicMatching.partner z x) = 1 / 2)
    (hr : ∀ e, 0 ≤ rate e)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (v : Site) (hv : ∀ R, v ∈ latticeBox R) (α : ℕ → ℝ≥0∞)
    (hcanonical : CanonicalOneArmEnergyBound z v α) :
    ∀ γ : ℝ, 0 < γ → γ < 31 / 36 → ∃ B : ℝ, 0 < B ∧ ∀ R, ∀ᶠ n in atTop,
      P.truncatedCorrelationEnergy (F n) (fun η => OneArm η v R) γ
        (volume.restrict (Ioc (0 : ℝ) 1)) ≤ ENNReal.ofReal B * (α R) ^ 2 := by
  intro γ hγ0 hγd
  obtain ⟨B, hB, H⟩ := hcanonical γ hγ0 hγd
  have hc : 0 < Real.exp 1 + 1 := by positivity
  refine ⟨(Real.exp 1 + 1) * B, mul_pos hc hB, ?_⟩
  intro R
  have H' := eventually_energy_le_canonical_bound P P (PeriodicMatching.partner z)
    (PeriodicMatching.partner_involutive z hz) (PeriodicMatching.partner_ne_self z hz)
    hhalf hr F hmono hex (latticeBox (R + 1)) (fun x _ => by rw [hhalf])
    (fun η => OneArm η v R) (fun _ _ he => oneArm_congr_of_eqOn_box (hv R) he)
    hγ0.le (by linarith : γ < 1) (H R)
  simpa only [ENNReal.ofReal_mul hc.le, mul_assoc] using H'

#print axioms finite_oneArm_energy_of_canonical_matching
#print axioms eventually_energy_le_canonical_bound
#print axioms finite_supported_time_aemeasurable

end ExceptionalTimes.FiniteMatchingExhaustion
