import ExceptionalTimes.FiniteClockBridge
import Mathlib.Probability.Distributions.Exponential

/-!
# Historical finite-Poisson-update contracts (unused by the proved identification)

The direct count-grid proof in `FiniteClockGridLaw` now proves the actual
retained-clock semigroup identity without either contract below. These
definitions are retained only as a documented abandoned interface.

Two inputs are kept separate. `CountRepresentationInput` is an UNPROVED
application target: passage from our interval-count encoding to an ordered
marked Poisson representation. Relevant sources are Last--Penrose (2017),
Proposition 2.10, Theorem 3.3, Proposition 6.9, Proposition 6.16 and Theorem
7.6. Applying those results still requires the counting-measure encoding
and its measurable-law uniqueness bridge; the source theorem alone is
NOT claimed to discharge this proposition.

`LPWFiniteUpdateInput` starts from independent exponential holding times
and iid update labels, matching Levin--Peres, *Markov Chains and Mixing
Times*, second edition (2017), §20.1, pp. 280--281, equations (20.1)--(20.8).
Neither input is an axiom or a proved theorem in this project.

The contract is universal over finite color cubes and finite injectively
indexed unordered edges. Its hypotheses give the full joint Poisson count
law, finite counts, clock support, and the literal chronological update
rule. It contains no percolation event, correlation bound, or dimension
assumption. The reduction below proves that the existing retained-clock
graphical model satisfies those hypotheses with exactly the same rates.
-/

open MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace ExceptionalTimes.PublishedFiniteCTMC

open FiniteClockBridge FiniteFractional FiniteGenerator

variable {Ξ I : Type*} [MeasurableSpace Ξ] [Fintype I]

/-- All initial finite colors and all disjoint selected clock-count tests
have their specified product probabilities. -/
def UniformFiniteClockLaw (μ : Measure Ξ) (V : Finset Site)
    (edge : I → V × V) (rate : Sym2 Site → ℝ)
    (initial : Ξ → V → Bool) (clocks : Ξ → ClockField) : Prop :=
  ∀ (η : V → Bool) (n : ℕ) (T : ClockTests n)
      (_hselected : ∀ i, T.edge i ∈ retainedEdges V edge) (count : Fin n → ℕ),
    μ {ω | initial ω = η ∧
      ∀ i, (clocks ω).markCount (T.edge i) (T.start i) (T.finish i) = count i} =
      (1 / 2 : ℝ≥0∞) ^ V.card *
        ∏ i, poissonMass (rate (T.edge i) * (T.finish i - T.start i)) (count i)

structure FiniteClockSystem (μ : Measure Ξ) (V : Finset Site)
    (edge : I → V × V) (rate : Sym2 Site → ℝ) where
  initial : Ξ → V → Bool
  clocks : Ξ → ClockField
  measurable_initial : Measurable initial
  measurable_counts : ∀ e a b, Measurable (fun ω => (clocks ω).markCount e a b)
  finite_counts : ∀ ω, (clocks ω).FiniteEdgeCounts
  supported : ∀ ω u v t, (clocks ω).Rings u v t → s(u, v) ∈ retainedEdges V edge
  independent_law : UniformFiniteClockLaw μ V edge rate initial clocks

/-- A process is tied to actual marks by the proved chronological sweep,
not by an assumed generator or a desired correlation formula. -/
def IsChronologicalVersion {μ : Measure Ξ} {V : Finset Site}
    {edge : I → V × V} {rate : Sym2 Site → ℝ}
    (S : FiniteClockSystem μ V edge rate) (Y : Ξ → ℝ → V → Bool) : Prop :=
  ∀ ω t events, IsSweep (S.clocks ω) (siteEdges V edge) (TimeCutoff.closedAt t) events →
    Y ω t = runColors edge events (S.initial ω)

noncomputable def totalRate (V : Finset Site) (edge : I → V × V)
    (rate : Sym2 Site → ℝ) : ℝ := ∑ i, rate (edgePair V edge i)

def arrivalTime (holding : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), holding k

def descendingEvents (holding : ℕ → ℝ) (label : ℕ → I) (n : ℕ) : List (ℝ × I) :=
  ((List.range n).map (fun k => (arrivalTime holding k, label k))).reverse

/-- An actual ordered representation of the same clocks, with precise
joint iid exponential/label laws independent of the initial cube. -/
structure HoldingRepresentation {μ : Measure Ξ} {V : Finset Site}
    {edge : I → V × V} {rate : Sym2 Site → ℝ}
    (S : FiniteClockSystem μ V edge rate) where
  holding : Ξ → ℕ → ℝ
  label : Ξ → ℕ → I
  count : Ξ → ℝ → ℕ
  holding_measurable : ∀ n, Measurable (fun ω => holding ω n)
  holding_positive : ∀ᵐ ω ∂μ, ∀ n, 0 < holding ω n
  count_spec : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ t → ∀ n,
    n < count ω t ↔ arrivalTime (holding ω) n ≤ t
  sweep : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ t →
    IsSweep (S.clocks ω) (siteEdges V edge) (TimeCutoff.closedAt t)
      (descendingEvents (holding ω) (label ω) (count ω t))
  joint_law : ∀ (η : V → Bool) (n : ℕ) (B : Fin n → Set ℝ),
    (∀ j, MeasurableSet (B j)) → ∀ indices : Fin n → I,
    μ {ω | S.initial ω = η ∧ ∀ j : Fin n,
      holding ω j ∈ B j ∧ label ω j = indices j} =
      (1 / 2 : ℝ≥0∞) ^ V.card * ∏ j,
        ProbabilityTheory.expMeasure (totalRate V edge rate) (B j) *
          ENNReal.ofReal (rate (edgePair V edge (indices j)) / totalRate V edge rate)

theorem HoldingRepresentation.noGlobalTies {μ : Measure Ξ} {V : Finset Site}
    {edge : I → V × V} {rate : Sym2 Site → ℝ}
    {S : FiniteClockSystem μ V edge rate} (R : HoldingRepresentation S) :
    ∀ᵐ ω ∂μ, NoGlobalTies (S.clocks ω) := by
  filter_upwards [R.sweep] with ω hsweep
  intro u v x y t huv hxy
  exact (hsweep t huv.pos.le).same_pair_at_cutoff huv hxy

/-- Unproved count-encoding application lemma. It is deliberately separate
from the published semigroup theorem; see the module source-boundary note.
The zero-total-rate case is excluded and must be treated separately. -/
def CountRepresentationInput (Ξ I : Type*) [MeasurableSpace Ξ] [Fintype I] : Prop :=
  ∀ (μ : Measure Ξ) [IsProbabilityMeasure μ] (V : Finset Site)
    (edge : I → V × V) (rate : Sym2 Site → ℝ),
    Function.Injective (edgePair V edge) →
    (∀ i, (edge i).1 ≠ (edge i).2) →
    (∀ i, 0 ≤ rate (edgePair V edge i)) →
    0 < totalRate V edge rate →
    ∀ S : FiniteClockSystem μ V edge rate, Nonempty (HoldingRepresentation S)

/-- Finite CTMC semigroup input after the literal exponential holding-time
and iid update-label representation has been supplied. -/
def LPWFiniteUpdateInput (Ξ I : Type*) [MeasurableSpace Ξ] [Fintype I] : Prop :=
  ∀ (μ : Measure Ξ) [IsProbabilityMeasure μ] (V : Finset Site)
    (edge : I → V × V) (rate : Sym2 Site → ℝ),
    Function.Injective (edgePair V edge) →
    (∀ i, (edge i).1 ≠ (edge i).2) →
    (∀ i, 0 ≤ rate (edgePair V edge i)) →
    0 < totalRate V edge rate →
    ∀ (S : FiniteClockSystem μ V edge rate) (Y : Ξ → ℝ → V → Bool),
      HoldingRepresentation S →
      IsChronologicalVersion S Y →
      ∀ t, 0 ≤ t →
        AEMeasurable (fun ω => Y ω t) μ ∧
        ∀ η ξ : V → Bool,
          μ {ω | S.initial ω = η ∧ Y ω t = ξ} =
            (1 / 2 : ℝ≥0∞) ^ V.card *
              ENNReal.ofReal ((NormedSpace.exp ((-t) •
                complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
                  (fun i => rate (edgePair V edge i)))) η ξ).re

/-- The concrete retained-clock model has the finite initial law and
independent counts required by the published finite theorem. -/
noncomputable def retainedSystem {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (V : Finset Site) (edge : I → V × V) :
    FiniteClockSystem μ V edge rate where
  initial ω := restrictColor V (P.initial ω)
  clocks ω := (P.clocks ω).restrictEdges (retainedEdges V edge)
  measurable_initial := by
    apply Measurable.of_eval
    intro v
    exact (measurable_pi_apply (v : Site)).comp P.measurable_initial
  measurable_counts e a b := by
    by_cases he : e ∈ retainedEdges V edge
    · simpa only [restricted_markCount_of_mem _ _ he] using P.measurable_counts e a b
    · have hz : (fun ω => ((P.clocks ω).restrictEdges (retainedEdges V edge)).markCount e a b) =
          fun _ => 0 := by
        funext ω
        simp [ClockField.markCount, ClockField.restrictEdges, he]
      rw [hz]
      exact measurable_const
  finite_counts ω := restricted_finite_counts (P.clocks ω) (P.finiteEdgeCounts ω) _
  supported ω u v t hr :=
    ((ClockField.restrictEdges_rings _ _ u v t).mp hr).1
  independent_law := by
    intro η n T hselected count
    simp_rw [restricted_markCount_of_mem _ _ (hselected _)]
    exact finiteCube_joint_counts V P.independent_law η n T count

theorem retained_chronological {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (V : Finset Site) (edge : I → V × V) :
    IsChronologicalVersion (retainedSystem P V edge)
      (fun ω t => projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t) := by
  intro ω t events hsweep
  exact projectedTrajectory_eq_sweep V (P.clocks ω) (P.finiteEdgeCounts ω)
    (P.no_incident_ties ω) edge (P.initial ω) t hsweep

/-- Conditional application of only the finite published theorem. The
graphical process, finite color cube, edge indexing, and rates are concrete.
The no-global-ties event is concluded a.e., never inserted into the model. -/
theorem retained_matrix_kernel
    (hcount : CountRepresentationInput Ξ I) (hLPW : LPWFiniteUpdateInput Ξ I)
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (V : Finset Site) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge))
    (hne : ∀ i, (edge i).1 ≠ (edge i).2)
    (hrate : ∀ i, 0 ≤ rate (edgePair V edge i))
    (htotal : 0 < totalRate V edge rate) :
    (∀ᵐ ω ∂μ, NoGlobalTies ((P.clocks ω).restrictEdges (retainedEdges V edge))) ∧
    ∀ t, 0 ≤ t →
      AEMeasurable (fun ω => projectedTrajectory V (P.clocks ω)
        (P.finiteEdgeCounts ω) edge (P.initial ω) t) μ ∧
      ∀ η ξ : V → Bool,
        μ {ω | restrictColor V (P.initial ω) = η ∧
          projectedTrajectory V (P.clocks ω) (P.finiteEdgeCounts ω) edge (P.initial ω) t = ξ} =
          (1 / 2 : ℝ≥0∞) ^ V.card *
            ENNReal.ofReal ((NormedSpace.exp ((-t) •
              complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
                (fun i => rate (edgePair V edge i)))) η ξ).re := by
  let _ : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  obtain ⟨R⟩ := hcount μ V edge rate hinj hne hrate htotal (retainedSystem P V edge)
  exact ⟨R.noGlobalTies, hLPW μ V edge rate hinj hne hrate htotal
    (retainedSystem P V edge) _ R (retained_chronological P V edge)⟩

#print axioms retained_chronological
#print axioms retained_matrix_kernel

end ExceptionalTimes.PublishedFiniteCTMC
