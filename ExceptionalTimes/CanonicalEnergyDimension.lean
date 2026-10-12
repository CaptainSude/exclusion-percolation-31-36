import ExceptionalTimes.FiniteMatchingExhaustion
import ExceptionalTimes.FiniteEdgeExhaustion
import ExceptionalTimes.FiniteEnergyDimension
import ExceptionalTimes.TruncatedMeasurability
import ExceptionalTimes.FiniteClockMarginal

/-! The finite-clock, finite-generator, matching-law, exhaustion, and Fatou
bridges are proved. The canonical matching energy estimate and full-process
properties below remain explicit obligations, not claimed published inputs. -/

namespace ExceptionalTimes.CanonicalEnergyDimension

open MeasureTheory Set Filter
open scoped ENNReal
open FiniteMatchingExhaustion FiniteEdgeExhaustion

theorem almostSureConjecturedDimension_of_canonical_energy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (hX : Measurable (fun p : Ω × ℝ => P.trajectories p.1 p.2))
    (z : Site) (hz : z ≠ (0, 0))
    (hhalf : ∀ x, rate s(x, PeriodicMatching.partner z x) = 1 / 2)
    (hr : ∀ e, 0 ≤ rate e)
    (v : Site) (hv : ∀ R, v ∈ latticeBox R)
    (α : ℕ → ℝ≥0∞) (hα : ∀ R, α R ≠ 0) (hαtop : ∀ R, α R ≠ ⊤)
    (hmarginal : ∀ R t, μ {ω | OneArm (P.trajectories ω t) v R} = α R)
    (hstationary : ∀ R s t, 0 ≤ s → 0 ≤ t →
      μ {ω | OneArm (P.trajectories ω s) v R ∧ OneArm (P.trajectories ω t) v R} =
        μ {ω | OneArm (P.trajectories ω 0) v R ∧
          OneArm (P.trajectories ω (dist s t)) v R})
    (hcanonical : CanonicalOneArmEnergyBound z v α)
    (hpreserve : ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (P.trajectories ω) v)
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (shift : Site)
    (hshift : Function.Semiconj P.trajectories e (translateTrajectory shift))
    (hupper : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (P.trajectories ω)) ≤ (31 / 36 : ℝ≥0∞)) :
    AlmostSureConjecturedDimension μ P.trajectories := by
  apply FiniteEnergyDimension.almostSureConjecturedDimension_of_finite_energy
    P hcapacity hX edges edges_monotone edges_exhaustive v hv α hα hαtop
    hmarginal hstationary
    (fun n t => P.aemeasurable_truncated hr (edges n) t)
    (fun n R γ => finite_supported_time_aemeasurable P hr (edges n) (latticeBox (R + 1))
      (fun η => OneArm η v R) (fun _ _ h => oneArm_congr_of_eqOn_box (hv R) h) γ)
    (finite_oneArm_energy_of_canonical_matching P z hz hhalf hr
      edges edges_monotone edges_exhaustive v hv α hcanonical)
    hpreserve e he shift hshift hupper

#print axioms almostSureConjecturedDimension_of_canonical_energy

theorem almostSureConjecturedDimension_of_fair_canonical_energy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (hX : Measurable (fun p : Ω × ℝ => P.trajectories p.1 p.2))
    (z : Site) (hz : z ≠ (0, 0))
    (hhalf : ∀ x, rate s(x, PeriodicMatching.partner z x) = 1 / 2)
    (hr : ∀ e, 0 ≤ rate e)
    (hstationary : ∀ R s t, 0 ≤ s → 0 ≤ t →
      μ {ω | OneArm (P.trajectories ω s) (0, 0) R ∧ OneArm (P.trajectories ω t) (0, 0) R} =
        μ {ω | OneArm (P.trajectories ω 0) (0, 0) R ∧
          OneArm (P.trajectories ω (dist s t)) (0, 0) R})
    (hcanonical : CanonicalOneArmEnergyBound z (0, 0) (FairOneArm.probability P))
    (hpreserve : ∀ᵐ ω ∂μ, TimeClosure.SiteClosurePreservesPercolationAt (P.trajectories ω) (0, 0))
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (shift : Site)
    (hshift : Function.Semiconj P.trajectories e (translateTrajectory shift))
    (hupper : ∀ᵐ ω ∂μ, dimH (exceptionalTimes (P.trajectories ω)) ≤ (31 / 36 : ℝ≥0∞)) :
    AlmostSureConjecturedDimension μ P.trajectories := by
  apply almostSureConjecturedDimension_of_canonical_energy P hcapacity hX z hz hhalf hr
    (0, 0) FairOneArm.origin_mem_latticeBox (FairOneArm.probability P)
    (fun R => (FairOneArm.probability_pos P R).ne') (FairOneArm.probability_ne_top P)
    (fun R t => FiniteClockMarginal.oneArm_marginal P hr edges edges_monotone edges_exhaustive
      (0, 0) R (FairOneArm.origin_mem_latticeBox R) t)
    hstationary hcanonical hpreserve e he shift hshift hupper

#print axioms almostSureConjecturedDimension_of_fair_canonical_energy

end ExceptionalTimes.CanonicalEnergyDimension

