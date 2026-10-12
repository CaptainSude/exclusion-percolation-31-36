import ExceptionalTimes.CanonicalProbeDecay
import ExceptionalTimes.CanonicalEnergyFromProbeDecay
import ExceptionalTimes.DecorrelationLength

/-! One fixed-aspect canonical arm-mixing statement supplies the complete
scale-dependent probe input. The integer decorrelation length is constructed.
The fixed-aspect statement is NEW and unproved; it is the intended output
of the calibrated finite-quad transfer, not an assumed literature theorem. -/

open scoped Classical

namespace ExceptionalTimes.FixedAspectEnergy

open PairSquareSewing CanonicalHexAnnuli ManyDimerLaw DimerLaw ActivePartitionLaw
open CanonicalEnergyFromProbeDecay

/-- The remaining new mixing statement, on literal finite matching laws
and covered, fixed-aspect hexagonal annuli. Its reference times have the
critical 3/4 scale with an arbitrary positive exponent loss. -/
def NewFixedAspectMixing (z : Site) : Prop :=
  ∃ M : ℕ,2≤M ∧ ∃ h : ℝ,0<h ∧ ∃ s₀ : ℕ,∃ reference : ℕ→ℝ,
    (∀ s,s₀≤s → 0≤reference s) ∧
    (∀ η : ℝ,0<η → η<3/4 → ∃ C : ℝ,0≤C ∧
      ∀ s,s₀≤s → reference s≤C*(s : ℝ)^(-(3/4-η))) ∧
    ∀ k : ℕ,∀ slot : Fin k×Fin 2 ↪ Site,
      (∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
      ∀ x s,s₀≤s →
        (∀ v∈CanonicalHexAnnuli.region x (s : ℤ) ((M*s : ℕ) : ℤ),∃ b,slot b=v) →
        manyProbability (fun _ => refreshProbability (reference s))
          (fun ω => HexFourArms x (s : ℤ) ((M*s : ℕ) : ℤ) (pairDecode slot ω)) ≤
            (2*(M : ℝ))^(-(2+h))

theorem scale_dependent_probe_decay_of_fixed_aspect
    (orderInput : Annulus.PublishedAnnularCrosscutOrder) (z : Site) (B₀ : ℕ)
    (hnew : NewFixedAspectMixing z) : NewScaleDependentProbeDecay z B₀ := by
  obtain ⟨M,hM,h,hh,s₀,reference,href0,hrefpower,hfixed⟩ := hnew
  intro η hη0 hη1 K hK
  obtain ⟨C,hC,href⟩ := hrefpower η hη0 hη1
  let base := max 1 (max B₀ (max (latticeRadius z) s₀))
  have hb1 : 1≤base := le_max_left _ _
  have hbB : B₀≤base := (le_max_left _ _).trans (le_max_right _ _)
  have hbd : latticeRadius z≤base :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hbs : s₀≤base :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨D,hD,m,hm⟩ := DecorrelationLength.exists_integer_scale base (by omega)
    hC (by linarith : 0<3/4-η) reference (fun s hs => href s (hbs.trans hs))
  refine ⟨(2*(M : ℝ)*32768)^(2+h),Real.rpow_nonneg (by positivity) _,
    h,hh,D,hD,m,?_⟩
  intro t ht
  obtain ⟨hbm,hmt,hrefm⟩ := hm t ht
  have hmpos : 0<m t := by omega
  have hdm : latticeRadius z≤m t := hbd.trans hbm
  refine ⟨hmpos,hbB.trans hbm,hdm,hmt,?_⟩
  intro k slot hpartner
  apply CanonicalProbeDecay.probe_decay_of_fixed_aspect orderInput slot z K (m t)
    (latticeRadius z) M hK hmpos hdm hM (mem_latticeBox_of_radius_le le_rfl) hpartner
    reference t h hh
  · intro s hs
    apply href0 s
    exact hbs.trans (hbm.trans (by omega))
  · intro s hs
    exact hrefm s (by omega)
  · intro x s hs hcover
    exact hfixed k slot hpartner x s (hbs.trans (hbm.trans (by omega))) hcover

#print axioms scale_dependent_probe_decay_of_fixed_aspect

end ExceptionalTimes.FixedAspectEnergy
