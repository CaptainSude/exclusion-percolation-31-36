import ExceptionalTimes.SpatialInvariance
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Algebra.Group.End

/-!
A measurable-witness route from positive probability to almost-sure dimension
in a fixed time window. The compactness/Frostman implication and the actual
spatial ergodicity of the graphical model remain explicit hypotheses.

No measurability of a Hausdorff-dimension event is assumed. We saturate a
measurable witness event under one invertible, measure-preserving ergodic
spatial shift, then transfer its almost-sure conclusion by set inclusion.
-/

namespace ExceptionalTimes.WindowUpgrade

open Set MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

def tailUnion (F : ℕ → Set Ω) (n : ℕ) : Set Ω := ⋃ m, ⋃ (_ : n ≤ m), F m

def witnessLimsup (F : ℕ → Set Ω) : Set Ω := ⋂ n, tailUnion F n

omit [MeasurableSpace Ω] in
theorem mem_witnessLimsup {F : ℕ → Set Ω} {ω : Ω} :
    ω ∈ witnessLimsup F ↔ ∀ n, ∃ m, n ≤ m ∧ ω ∈ F m := by
  simp [witnessLimsup, tailUnion]

theorem measurableSet_tailUnion {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet (F n))
    (n : ℕ) : MeasurableSet (tailUnion F n) :=
  MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hF m

theorem measurableSet_witnessLimsup {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet (F n)) :
    MeasurableSet (witnessLimsup F) :=
  MeasurableSet.iInter (measurableSet_tailUnion hF)

omit [MeasurableSpace Ω] in
theorem tailUnion_antitone (F : ℕ → Set Ω) : Antitone (tailUnion F) := by
  intro n m hnm ω hω
  simp only [tailUnion, mem_iUnion] at hω ⊢
  obtain ⟨k, hmk, hk⟩ := hω
  exact ⟨k, hnm.trans hmk, hk⟩

/-- Continuity from above gives the limsup lower bound without any independence
among the witness events. -/
theorem le_measure_witnessLimsup (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet (F n)) {c : ℝ≥0∞}
    (hc : ∀ n, c ≤ μ (F n)) : c ≤ μ (witnessLimsup F) := by
  unfold witnessLimsup
  rw [(tailUnion_antitone F).measure_iInter
    (fun n => (measurableSet_tailUnion hF n).nullMeasurableSet)
    ⟨0, measure_ne_top μ _⟩]
  apply le_iInf
  intro n
  apply (hc n).trans
  apply measure_mono
  intro ω hω
  exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨le_refl n, hω⟩⟩

theorem measurable_perm_zpow (e : Ω ≃ᵐ Ω) (n : ℤ) :
    Measurable ((e.toEquiv ^ n : Equiv.Perm Ω) : Ω → Ω) := by
  cases n with
  | ofNat n =>
      change Measurable (e : Ω → Ω)^[n]
      exact e.measurable.iterate n
  | negSucc n =>
      rw [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def]
      change Measurable (e.symm : Ω → Ω)^[n + 1]
      exact e.symm.measurable.iterate (n + 1)

/-- Countably many integer translates of a measurable witness. -/
def spatialSaturation (e : Ω ≃ᵐ Ω) (F : Set Ω) : Set Ω :=
  ⋃ n : ℤ, ((e.toEquiv ^ n : Equiv.Perm Ω) : Ω → Ω) ⁻¹' F

theorem mem_spatialSaturation {e : Ω ≃ᵐ Ω} {F : Set Ω} {ω : Ω} :
    ω ∈ spatialSaturation e F ↔ ∃ n : ℤ, (e.toEquiv ^ n) ω ∈ F := by
  simp [spatialSaturation]

theorem measurableSet_spatialSaturation (e : Ω ≃ᵐ Ω) {F : Set Ω}
    (hF : MeasurableSet F) : MeasurableSet (spatialSaturation e F) :=
  MeasurableSet.iUnion (fun n => hF.preimage (measurable_perm_zpow e n))

theorem subset_spatialSaturation (e : Ω ≃ᵐ Ω) (F : Set Ω) : F ⊆ spatialSaturation e F := by
  intro ω hω
  apply mem_spatialSaturation.mpr
  exact ⟨0, by simpa using hω⟩

theorem spatialSaturation_invariant (e : Ω ≃ᵐ Ω) (F : Set Ω) :
    e ⁻¹' spatialSaturation e F = spatialSaturation e F := by
  ext ω
  change e ω ∈ spatialSaturation e F ↔ ω ∈ spatialSaturation e F
  rw [mem_spatialSaturation, mem_spatialSaturation]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    change (e.toEquiv ^ n) (e.toEquiv ω) ∈ F at hn
    simpa only [zpow_add, zpow_one, Equiv.Perm.mul_apply] using hn
  · rintro ⟨n, hn⟩
    refine ⟨n - 1, ?_⟩
    change (e.toEquiv ^ (n - 1)) (e.toEquiv ω) ∈ F
    simpa only [zpow_sub, zpow_one, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply] using hn

/-- A positive measurable witness has almost-sure spatial saturation under an
actual ergodic measure-preserving transformation. -/
theorem ae_mem_spatialSaturation (μ : Measure Ω) (e : Ω ≃ᵐ Ω)
    (he : Ergodic e μ) {F : Set Ω} (hF : MeasurableSet F) (hp : 0 < μ F) :
    ∀ᵐ ω ∂μ, ω ∈ spatialSaturation e F := by
  have hpos : 0 < μ (spatialSaturation e F) :=
    hp.trans_le (measure_mono (subset_spatialSaturation e F))
  rcases he.toPreErgodic.measure_self_or_compl_eq_zero
    (measurableSet_spatialSaturation e hF) (spatialSaturation_invariant e F) with h | h
  · exact (ne_of_gt hpos h).elim
  · exact ae_iff.mpr h

theorem invariant_property_zpow (e : Ω ≃ᵐ Ω) {P : Ω → Prop}
    (hP : ∀ ω, P (e ω) ↔ P ω) (n : ℤ) (ω : Ω) :
    P ((e.toEquiv ^ n) ω) ↔ P ω := by
  have h : ∀ ω, P ((e.toEquiv ^ n) ω) ↔ P ω := by
    apply zpow_induction_left (P := fun a : Equiv.Perm Ω => ∀ ω, P (a ω) ↔ P ω)
    · intro ω
      rfl
    · intro a ha ω
      exact (hP (a ω)).trans (ha ω)
    · intro a ha ω
      have hi : P (e.symm (a ω)) ↔ P (a ω) := by
        simpa only [MeasurableEquiv.apply_symm_apply] using (hP (e.symm (a ω))).symm
      exact hi.trans (ha ω)
  exact h ω

theorem spatialSaturation_subset_of_invariant (e : Ω ≃ᵐ Ω) {F : Set Ω} {P : Ω → Prop}
    (hP : ∀ ω, P (e ω) ↔ P ω) (hF : ∀ ω ∈ F, P ω) :
    spatialSaturation e F ⊆ {ω | P ω} := by
  intro ω hω
  obtain ⟨n, hn⟩ := mem_spatialSaturation.mp hω
  exact (invariant_property_zpow e hP n ω).mp (hF _ hn)

/-- Generic measurable-witness upgrade. The target predicate need not be
measurable; the measurable almost-sure set constructed here implies it. -/
theorem ae_invariant_property_of_witnesses (μ : Measure Ω) [IsFiniteMeasure μ]
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ)
    {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet (F n))
    {c : ℝ≥0∞} (hc : 0 < c) (hprob : ∀ n, c ≤ μ (F n))
    {P : Ω → Prop} (hP : ∀ ω, P (e ω) ↔ P ω)
    (hwitness : ∀ ω ∈ witnessLimsup F, P ω) : ∀ᵐ ω ∂μ, P ω := by
  have hp : 0 < μ (witnessLimsup F) := hc.trans_le (le_measure_witnessLimsup μ hF hprob)
  exact (ae_mem_spatialSaturation μ e he (measurableSet_witnessLimsup hF) hp).mono
    (fun ω hω => spatialSaturation_subset_of_invariant e hP hwitness hω)

/-- The fixed-window lower-dimension upgrade for actual lattice trajectories.

`hwitness` is deliberately explicit: applying the SS compactness criterion
and GV closure lemma to occupation measures is a separate, outstanding proof.
Likewise `he` requires actual spatial ergodicity of the model; no such property
is inferred merely from its name or its finite-dimensional law specification.
This theorem assumes no measurability of the random dimension event. -/
theorem ae_window_lowerDimension_of_witnesses (μ : Measure Ω) [IsFiniteMeasure μ]
    (e : Ω ≃ᵐ Ω) (he : Ergodic e μ) (X : Ω → Trajectory) (z : Site)
    (hshift : Function.Semiconj X e (translateTrajectory z))
    {F : ℕ → Set Ω} (hF : ∀ n, MeasurableSet (F n))
    {c : ℝ≥0∞} (hc : 0 < c) (hprob : ∀ n, c ≤ μ (F n))
    (J : Set ℝ) (d : ℝ≥0∞)
    (hwitness : ∀ ω ∈ witnessLimsup F, d ≤ dimH (exceptionalTimes (X ω) ∩ J)) :
    ∀ᵐ ω ∂μ, d ≤ dimH (exceptionalTimes (X ω) ∩ J) := by
  apply ae_invariant_property_of_witnesses μ e he hF hc hprob _ hwitness
  intro ω
  rw [hshift ω, exceptionalTimes_translate]

end ExceptionalTimes.WindowUpgrade

#print axioms ExceptionalTimes.WindowUpgrade.le_measure_witnessLimsup
#print axioms ExceptionalTimes.WindowUpgrade.ae_mem_spatialSaturation
#print axioms ExceptionalTimes.WindowUpgrade.ae_window_lowerDimension_of_witnesses
