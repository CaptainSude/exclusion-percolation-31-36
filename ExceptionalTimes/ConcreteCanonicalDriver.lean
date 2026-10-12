import ExceptionalTimes.KernelDimensionReduction
import ExceptionalTimes.PublishedPoissonConstruction
import ExceptionalTimes.PublishedExclusionUpper
import ExceptionalTimes.ProbeProduct

/-! Concrete conditional main driver. The three named construction/upper-bound
inputs and the Schramm--Steif capacity criterion are published results.
`NewCanonicalEnergy` is a separate NEW, UNPROVED percolation estimate; this
module does not claim a published-input-only proof of the dimension theorem.

The normalization in that remaining estimate is the literal finite iid fair
one-arm probability. It is independent of the chosen clock law or realization.
The finite-law dictionary below identifies it with every actual realization's
initial and fixed-time marginal probabilities.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ExceptionalTimes.ConcreteCanonicalDriver

open FiniteClockBridge EnvironmentVariance ProbeProduct
open FiniteMatchingExhaustion CanonicalEdgeIndex CanonicalBlockLaw
open PublishedPoissonConstruction PublishedExclusionUpper

noncomputable def finiteFairOneArm (R : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (EnvironmentVariance.probability (fairSites (latticeBox (R+1)))
    (fun η => OneArm (extendColor (latticeBox (R+1)) η) (0,0) R))

theorem initial_local_probability_eq_fair
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (D : Finset Site)
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ v ∈ D, η v = ξ v) → (E η ↔ E ξ)) :
    μ {ω | E (P.initial ω)} =
      ENNReal.ofReal (EnvironmentVariance.probability (fairSites D)
        (fun η => E (extendColor D η))) := by
  let X := fun ω => restrictColor D (P.initial ω)
  let A : Finset (D → Bool) := Finset.univ.filter (fun η => E (extendColor D η))
  have hX : Measurable X := Measurable.of_eval (fun v =>
    (measurable_pi_apply (v : Site)).comp P.measurable_initial)
  have hset : {ω | E (P.initial ω)} = X ⁻¹' (A : Set (D → Bool)) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe,
      A, Finset.mem_filter, Finset.mem_univ, true_and]
    apply hlocal
    intro v hv
    simp [X,extendColor,restrictColor,hv]
  have hatom (η : D → Bool) : μ (X ⁻¹' {η}) = (1/2 : ℝ≥0∞)^D.card := by
    change μ {ω | restrictColor D (P.initial ω) = η} = _
    simp only [restrictColor_eq_iff]
    exact P.independent_law.fair_initial D (extendColor D η)
  rw [hset, ← sum_measure_preimage_singleton A
    (fun η _ => hX (measurableSet_singleton η))]
  simp_rw [hatom]
  rw [EnvironmentVariance.probability, FiniteLaw.expect,
    ENNReal.ofReal_sum_of_nonneg (fun η _ =>
      mul_nonneg ((fairSites D).nonneg η) (indicator_nonneg _))]
  simp only [A, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro η _
  by_cases h : E (extendColor D η)
  · simp only [h,ite_true,indicator,mul_one]
    simp [fairSites,FiniteLaw.pi,ProbeProduct.fairBit,ENNReal.ofReal_pow]
    norm_num [← ENNReal.inv_pow]
  · simp [h,indicator]

theorem probability_eq_finiteFairOneArm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) :
    FairOneArm.probability P = finiteFairOneArm := by
  funext R
  exact initial_local_probability_eq_fair P (latticeBox (R+1))
    (fun η => OneArm η (0,0) R)
    (fun _ _ h => oneArm_congr_of_eqOn_box (FairOneArm.origin_mem_latticeBox R) h)

theorem oneArm_marginal_eq_finiteFairOneArm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (k : RateKernel) (P : PoissonGraphicalRealization μ k.unorderedPairRate)
    (R : ℕ) (t : ℝ) :
    μ {ω | OneArm (P.trajectories ω t) (0,0) R} = finiteFairOneArm R := by
  rw [FiniteClockMarginal.oneArm_marginal P (FiniteMatchingNormalization.unorderedPairRate_nonneg k)
    FiniteEdgeExhaustion.edges FiniteEdgeExhaustion.edges_monotone
    FiniteEdgeExhaustion.edges_exhaustive (0,0) R
    (FairOneArm.origin_mem_latticeBox R) t]
  exact congrFun (probability_eq_finiteFairOneArm P) R

/-- NEW and unproved. This is the remaining canonical matching-energy
estimate, with a process-independent finite fair-site normalization. -/
def NewCanonicalEnergy (k : RateKernel) : Prop :=
  ∀ z : Site, 0 < k.rate z →
    CanonicalOneArmEnergyBound z (0,0) finiteFairOneArm

/-- A concrete iid clock/color realization has the every-window 31/36
dimension conclusion, conditional on the visibly separate NEW energy estimate.
There are no additional process, stationarity, ergodicity, closure, or upper
bound placeholders beyond the three named literature inputs and capacity. -/
theorem exists_realization_dimension_of_new_canonical_energy
    (hpoisson : PositivePoissonMarks)
    (hgraphical : NormalizedGraphicalRegularity)
    (hupper : NormalizedDimensionUpper.{0})
    (hcapacity : PublishedCapacity.SchrammSteifCapacity)
    (k : RateKernel) (hnew : NewCanonicalEnergy k) :
    ∃ (ν : Displacement → Measure PositiveMarks),
      (∀ z, IsProbabilityMeasure (ν z)) ∧
      ∃ P : PoissonGraphicalRealization (law ν) k.unorderedPairRate,
        P.initial = initial ∧
        Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
        Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
          (translateTrajectory (1,0)) ∧
        AlmostSureConjecturedDimension (law ν) P.trajectories := by
  obtain ⟨ν,hν,P,hi,he,hs⟩ := exists_canonical_realization hpoisson hgraphical k
  refine ⟨ν,hν,P,hi,he,hs,?_⟩
  apply KernelDimensionReduction.almostSureConjecturedDimension_of_matching_energy
    k P hcapacity ?_ (ProductSpatialShift.translation (1,0)) he (1,0) hs
    (dimension_upper hupper k P)
  simpa only [probability_eq_finiteFairOneArm] using (show
    ∀ z : Site, 0 < k.rate z → CanonicalOneArmEnergyBound z (0,0) finiteFairOneArm from hnew)

#print axioms initial_local_probability_eq_fair
#print axioms probability_eq_finiteFairOneArm
#print axioms oneArm_marginal_eq_finiteFairOneArm
#print axioms exists_realization_dimension_of_new_canonical_energy

end ExceptionalTimes.ConcreteCanonicalDriver
