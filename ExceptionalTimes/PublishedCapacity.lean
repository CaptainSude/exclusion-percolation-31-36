import ExceptionalTimes.OccupationMoments
import ExceptionalTimes.TimeClosure
import ExceptionalTimes.WindowUpgrade

/-!
One precisely stated published input and its application to literal one-arm
occupation measures. Source: Schramm--Steif, Ann. Math. 171 (2010), Lemma 6.2,
p.650: decreasing compact subsets of [0,1], measures carried by them, and
infinitely many common positive-mass / bounded-energy witnesses.

`SchrammSteifCapacity` is a proposition supplied explicitly to the theorems;
it is not a new Lean axiom. The probability lower bound for the witness events
and the process-specific GV site-closure property remain explicit obligations.
-/

namespace ExceptionalTimes.PublishedCapacity

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
open OccupationMoments TimeClosure WindowUpgrade

/-- The deterministic published capacity criterion, restricted to finite
Borel measures on the real line. Energy uses the extended kernel with its
infinite diagonal. `∀ N, ∃ n ≥ N` expresses infinitely many witnesses. -/
def SchrammSteifCapacity : Prop :=
  ∀ (γ : ℝ), 0 < γ → ∀ (D : ℕ → Set ℝ),
    Antitone D → (∀ n, IsCompact (D n)) → (∀ n, D n ⊆ Icc 0 1) →
    ∀ (σ : ℕ → Measure ℝ), (∀ n, IsFiniteMeasure (σ n)) →
    (∀ n, σ n (D n)ᶜ = 0) →
    ∀ (C : ℝ), 0 < C →
    (∀ N : ℕ, ∃ n, N ≤ n ∧ ENNReal.ofReal (1 / C) < σ n univ ∧
      frostmanEnergy γ (σ n) ≤ ENNReal.ofReal C) →
    ENNReal.ofReal γ ≤ dimH (⋂ n, D n)

def armTimeSet (X : Trajectory) (v : Site) (R : ℕ) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧ OneArm (X t) v R}

def closedArmTimeSet (X : Trajectory) (v : Site) (R : ℕ) : Set ℝ :=
  closure (armTimeSet X v R)

theorem closedArmTimeSet_subset (X : Trajectory) (v : Site) (R : ℕ) :
    closedArmTimeSet X v R ⊆ Icc 0 1 :=
  closure_minimal (fun _ ht => ht.1) isClosed_Icc

theorem isCompact_closedArmTimeSet (X : Trajectory) (v : Site) (R : ℕ) :
    IsCompact (closedArmTimeSet X v R) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (closedArmTimeSet_subset X v R)

theorem closedArmTimeSet_antitone (X : Trajectory) (v : Site) :
    Antitone (closedArmTimeSet X v) := by
  intro n m hnm
  apply closure_mono
  intro t ht
  exact ⟨ht.1, oneArm_radius_mono hnm ht.2⟩

/-- This reduction uses the proved finite-cylinder closure bridge. Its only
remaining path hypothesis is the literal site-closure percolation property. -/
theorem closedArmTimeSet_iInter_subset (X : Trajectory) (v : Site)
    (hpreserve : SiteClosurePreservesPercolationAt X v) :
    (⋂ R, closedArmTimeSet X v R) ⊆ exceptionalTimes X ∩ Icc 0 1 := by
  intro t ht
  have hJ := closedArmTimeSet_subset X v 0 (mem_iInter.mp ht 0)
  refine ⟨exceptional_of_all_radius_closures_of_percolation X v hpreserve hJ.1 ?_, hJ⟩
  intro R
  apply closure_mono (s := armTimeSet X v R) _ (mem_iInter.mp ht R)
  intro s hs
  exact ⟨hs.1.1, hs.2⟩

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def unitOccupation (X : Ω → Trajectory) (v : Site)
    (c : ℕ → ℝ≥0∞) (R : ℕ) (ω : Ω) : Measure ℝ :=
  occupation (volume.restrict (Icc 0 1)) (c R) (oneArmEvent X v R) ω

theorem unitOccupation_finite (X : Ω → Trajectory)
    (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2)) (v : Site)
    (c : ℕ → ℝ≥0∞) (hc : ∀ R, c R ≠ ⊤) (R : ℕ) (ω : Ω) :
    IsFiniteMeasure (unitOccupation X v c R ω) := by
  rw [unitOccupation, occupation_eq_smul_restrict _ _ (measurableSet_oneArmEvent hX v R)]
  exact Measure.smul_finite _ (hc R)

theorem unitOccupation_carried (X : Ω → Trajectory)
    (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2)) (v : Site)
    (c : ℕ → ℝ≥0∞) (R : ℕ) (ω : Ω) :
    unitOccupation X v c R ω (closedArmTimeSet (X ω) v R)ᶜ = 0 := by
  rw [unitOccupation, occupation_eq_smul_restrict _ _ (measurableSet_oneArmEvent hX v R)]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hs : MeasurableSet {t | (ω, t) ∈ oneArmEvent X v R} :=
    (measurableSet_oneArmEvent hX v R).preimage (by fun_prop)
  have hclosed : MeasurableSet (closedArmTimeSet (X ω) v R)ᶜ :=
    isClosed_closure.measurableSet.compl
  rw [Measure.restrict_restrict hs, Measure.restrict_apply hclosed]
  have hempty : (closedArmTimeSet (X ω) v R)ᶜ ∩
      ({t | (ω, t) ∈ oneArmEvent X v R} ∩ Icc 0 1) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact ht.1 (subset_closure (show t ∈ armTimeSet (X ω) v R from ⟨ht.2.2, ht.2.1⟩))
  rw [hempty, measure_empty, mul_zero]

def occupationSuccess (X : Ω → Trajectory) (v : Site)
    (c : ℕ → ℝ≥0∞) (γ C : ℝ) (R : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal (1 / C) < unitOccupation X v c R ω univ ∧
    frostmanEnergy γ (unitOccupation X v c R ω) ≤ ENNReal.ofReal C}

theorem measurableSet_occupationSuccess (X : Ω → Trajectory)
    (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2)) (v : Site)
    (c : ℕ → ℝ≥0∞) (γ C : ℝ) (R : ℕ) :
    MeasurableSet (occupationSuccess X v c γ C R) := by
  have hm := measurable_occupation_mass (volume.restrict (Icc 0 1)) (c R)
    (measurableSet_oneArmEvent hX v R)
  have he := measurable_occupation_energy (volume.restrict (Icc 0 1)) (c R)
    (measurableSet_oneArmEvent hX v R) (measurable_frostmanKernel γ)
  exact (measurableSet_lt measurable_const hm).inter (measurableSet_le he measurable_const)

theorem dimension_of_occupation_limsup (hcapacity : SchrammSteifCapacity)
    (X : Ω → Trajectory) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
    (v : Site) (c : ℕ → ℝ≥0∞) (hc : ∀ R, c R ≠ ⊤)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C) (ω : Ω)
    (hpreserve : SiteClosurePreservesPercolationAt (X ω) v)
    (hω : ω ∈ witnessLimsup (occupationSuccess X v c γ C)) :
    ENNReal.ofReal γ ≤ dimH (exceptionalTimes (X ω) ∩ Icc 0 1) := by
  apply le_trans _ (dimH_mono (closedArmTimeSet_iInter_subset (X ω) v hpreserve))
  apply hcapacity γ hγ (closedArmTimeSet (X ω) v)
    (closedArmTimeSet_antitone (X ω) v) (isCompact_closedArmTimeSet (X ω) v)
    (closedArmTimeSet_subset (X ω) v) (fun R => unitOccupation X v c R ω)
    (fun R => unitOccupation_finite X hX v c hc R ω)
    (fun R => unitOccupation_carried X hX v c R ω) C hC
  exact mem_witnessLimsup.mp hω

end ExceptionalTimes.PublishedCapacity

#print axioms ExceptionalTimes.PublishedCapacity.unitOccupation_carried
#print axioms ExceptionalTimes.PublishedCapacity.dimension_of_occupation_limsup

