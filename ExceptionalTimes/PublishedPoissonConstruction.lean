import ExceptionalTimes.CanonicalRealization

/-! Two separate classical construction inputs, expressed on the literal
clock representation. These are propositions supplied as hypotheses, not
axioms. Neither contains a percolation estimate or any process-property
package.

`PositivePoissonMarks` is the positive-half-line specialization of
Last--Penrose, Definition 3.1, Theorem 3.6 and Proposition 6.9. The intensity
is rate times Lebesgue measure; its bounded intervals have finite mass and
its atoms have mass zero. Passing from the simple counting measure to its
point set retains exactly the interval-count sigma-algebra used here.
Zero rate is proved internally using the empty point set.

`NormalizedGraphicalRegularity` is only the path statement in
Garban--Vanneuville, Appendix A, items 1(a) and 2, for a symmetric transition
matrix whose rows sum to one. The raw iid clock law and its unordered-pair
indexing have already been proved in CanonicalClockField. No stationarity,
ergodicity, joint measurability, closed-color preservation, semigroup
identification, or dimension conclusion is included in this input.

Sources:
https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf
https://arxiv.org/pdf/1605.04766v3
-/

open MeasureTheory

namespace ExceptionalTimes.PublishedPoissonConstruction

open CanonicalEdgeIndex CanonicalBlockLaw CanonicalClockField

def PositivePoissonMarks : Prop :=
  ∀ rate : ℝ, 0 < rate → ∃ ν : Measure PositiveMarks,
    IsProbabilityMeasure ν ∧ PositiveMarks.HasPoissonCounts ν rate

def NormalizedGraphicalRegularity : Prop :=
  ∀ k : RateKernel, k.mass = 1 →
    ∀ (ν : Displacement → Measure PositiveMarks),
      (∀ z, IsProbabilityMeasure (ν z)) →
      (∀ z, PositiveMarks.HasPoissonCounts (ν z) (k.rate z.val)) →
      ∀ᵐ ω ∂law ν,
        (clocks ω).NoIncidentTies ∧ (clocks ω).HasClosedBackwardTraces

theorem exists_clock_law (h : PositivePoissonMarks) (rate : ℝ) (hrate : 0 ≤ rate) :
    ∃ ν : Measure PositiveMarks,
      IsProbabilityMeasure ν ∧ PositiveMarks.HasPoissonCounts ν rate := by
  rcases eq_or_lt_of_le hrate with hr | hr
  · subst rate
    exact ⟨Measure.dirac PositiveMarks.empty,inferInstance,PositiveMarks.empty_hasPoissonCounts⟩
  · exact h rate hr

theorem exists_canonical_realization (hpoisson : PositivePoissonMarks)
    (hgraphical : NormalizedGraphicalRegularity) (k : RateKernel) :
    ∃ (ν : Displacement → Measure PositiveMarks),
      (∀ z, IsProbabilityMeasure (ν z)) ∧
      ∃ P : PoissonGraphicalRealization (law ν) k.unorderedPairRate,
        P.initial = initial ∧
        Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
        Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
          (translateTrajectory (1,0)) := by
  choose ν hν hcounts using fun z : Displacement =>
    exists_clock_law hpoisson (k.normalized.rate z.val) (k.normalized.nonneg z.val)
  let : ∀ z, IsProbabilityMeasure (ν z) := hν
  refine ⟨ν,hν,?_⟩
  exact CanonicalRealization.exists_from_normalized_closed_traces k ν hcounts
    (hgraphical k.normalized k.normalized_mass ν hν hcounts)

#print axioms exists_canonical_realization

end ExceptionalTimes.PublishedPoissonConstruction
