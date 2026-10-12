import ExceptionalTimes.CanonicalClockField
import ExceptionalTimes.BernoulliShift
import ExceptionalTimes.ClockClosedTrace

/-! Canonical realization from single-clock Poisson laws and a.e. closed
backward traces. Spatial ergodicity is proved internally. The normalized
version retains the row-sum-one scope of GV Appendix A and then changes
time by the kernel mass. No percolation estimate is assumed or proved. -/

open MeasureTheory

namespace ExceptionalTimes.CanonicalRealization

open CanonicalEdgeIndex CanonicalBlockLaw CanonicalClockField

theorem exists_from_closed_traces (k : RateKernel)
    (ν : Displacement → Measure PositiveMarks) [∀ z, IsProbabilityMeasure (ν z)]
    (hlaw : ∀ z, PositiveMarks.HasPoissonCounts (ν z) (k.rate z.val))
    (hregular : ∀ᵐ ω ∂law ν,
      (clocks ω).NoIncidentTies ∧ (clocks ω).HasClosedBackwardTraces) :
    ∃ P : PoissonGraphicalRealization (law ν) k.unorderedPairRate,
      P.initial = initial ∧ P.clocks =ᵐ[law ν] clocks ∧
      Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
      Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
        (translateTrajectory (1,0)) := by
  apply exists_ergodic_realization k ν hlaw
  · exact hregular.mono fun ω hω =>
      ⟨hω.1,(clocks ω).hasFiniteBackwardTraces_of_closed hω.1 hω.2⟩
  · exact ProductSpatialShift.ergodic_shift (ProductSpatialShift.columnLaw (blockLaw ν))

theorem normalized_unordered_rate (k : RateKernel) :
    (fun e => k.mass * k.normalized.unorderedPairRate e) = k.unorderedPairRate := by
  funext e
  refine Sym2.inductionOn e ?_
  intro u v
  exact k.rate_from_normalized (v-u)

theorem exists_from_normalized_closed_traces (k : RateKernel)
    (ν : Displacement → Measure PositiveMarks) [∀ z, IsProbabilityMeasure (ν z)]
    (hlaw : ∀ z, PositiveMarks.HasPoissonCounts (ν z) (k.normalized.rate z.val))
    (hregular : ∀ᵐ ω ∂law ν,
      (clocks ω).NoIncidentTies ∧ (clocks ω).HasClosedBackwardTraces) :
    ∃ P : PoissonGraphicalRealization (law ν) k.unorderedPairRate,
      P.initial = initial ∧
      Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
      Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
        (translateTrajectory (1,0)) := by
  obtain ⟨P,hinit,_,he,hshift⟩ := exists_from_closed_traces k.normalized ν hlaw hregular
  have H : ∃ Q : PoissonGraphicalRealization (law ν)
      (fun e => k.mass * k.normalized.unorderedPairRate e),
      Q.initial = initial ∧
      Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
      Function.Semiconj Q.trajectories (ProductSpatialShift.translation (1,0))
        (translateTrajectory (1,0)) := by
    refine ⟨P.speedup k.mass k.mass_pos,hinit,he,?_⟩
    intro ω
    simp only [P.speedup_trajectories]
    funext t v
    exact congrFun (congrFun (hshift ω) (k.mass*t)) v
  rwa [normalized_unordered_rate] at H

#print axioms exists_from_closed_traces
#print axioms exists_from_normalized_closed_traces

end ExceptionalTimes.CanonicalRealization
