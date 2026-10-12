import ExceptionalTimes.FixedMeshSelectedForest
import ExceptionalTimes.ForestGeometryEnvelope
import ExceptionalTimes.ActualProductTransfer
import ExceptionalTimes.StaticHexApproximation
import ExceptionalTimes.DimerProbabilityDictionary

/-! Exact Boolean word tests and the degree-zero completion of the actual
selected forest bound. No probability estimate is assumed in these finite
algebraic adapters. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.WordForestGeometry
noncomputable section
open PairSquareSewing EnvironmentVariance CenteredBlocks BlockExpansion
open SelectedPerturbation DimerLaw DimerExpansion CanonicalSpatialProduct
open ForestGeometryEnvelope NormalizedForestProfile

def wordOuter {F : Type*} (word : (F→Bool)→Bool) (x : F×Bool→Bool) : ℝ :=
  indicator (word (fun i => x (i,false))=true ∧ word (fun i => x (i,true))=true)

theorem wordOuter_abs_le_one {F : Type*} (word : (F→Bool)→Bool) (x : F×Bool→Bool) :
    |wordOuter word x|≤1 := by
  rw [wordOuter,abs_of_nonneg (indicator_nonneg _)]
  exact indicator_le_one _

theorem wordOuter_pairedTest {B : Type*} [Fintype B] {q : ℕ}
    (T : DyadicQuadFamily (Fin q)) (n : ℕ) (word : (Fin q→Bool)→Bool)
    (slot : B×Fin 2 ↪ Site) (h : B→History) :
    wordOuter word (fun qt => T.test n qt.1
      (canonicalBackground slot (pairCoordinates.symm h) qt.2))=
      DimerProbabilityDictionary.pairedTest slot
        (StaticHexApproximation.wordEvent T n word) h := rfl

variable {B H J : Type*} [Fintype B] [Fintype H] [Fintype J]

omit [Fintype J] in
theorem selected_empty_abs_le_one (μ : B→FiniteLaw H) (f : (B→H)→ℝ)
    (hf : ∀ x,|f x|≤1) (u : B→H→ℝ) :
    |selectedKernel (fun b => (μ b).weight) u ∅ f|≤1 := by
  rw [PerturbationControl.selectedKernel_empty]
  change |(FiniteLaw.pi μ).expect f|≤1
  exact ((FiniteLaw.pi μ).abs_expect_le f).trans
    (by simpa using (FiniteLaw.pi μ).expect_mono hf)

omit [Fintype J] in
theorem geometryBound_of_nonempty (μ : B→FiniteLaw H) (f : (B→H)→ℝ)
    (G : Finset B→ℝ) (hf : ∀ x,|f x|≤1) (hzero : G ∅=1)
    (hpos : ∀ S : Finset B,S.Nonempty → ∀ u : B→H→ℝ,
      (∀ b,∑ h,u b h=0) →
      |selectedKernel (fun b => (μ b).weight) u S f|≤
        (∏ b : S,variation (u b.val))*G S) : GeometryBound μ f G := by
  intro S u hu
  by_cases hS : S=∅
  · subst S
    simpa only [hzero,Finset.prod_empty,mul_one] using selected_empty_abs_le_one μ f hf u
  · have hh := hpos S (Finset.nonempty_iff_ne_empty.mpr hS) u hu
    rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
    simpa only [mul_comm] using hh

omit [Fintype H] in
theorem envelope_geometryBound (G : (S : Finset B)→DimerGeometry S J)
    (cutoff stop D C K g : ℝ) (p : ℝ→ℝ) (f : (B→History)→ℝ)
    (hf : ∀ x,|f x|≤1)
    (hpos : ∀ S : Finset B,S.Nonempty → ∀ u : B→History→ℝ,
      (∀ b,∑ h,u b h=0) →
      |selectedKernel (fun _ => base) u S f|≤
        (∏ b : S,variation (u b.val))*canonicalForestValue (G S) cutoff
          (OptimizedForestStop.radius stop D S.card) C K g
          (normalized p (OptimizedForestStop.radius stop D S.card))) :
    GeometryBound (fun _ => ActualProductTransfer.baseLaw) f
      (envelope G cutoff stop D C K g p) := by
  apply geometryBound_of_nonempty _ f _ hf (envelope_empty ..)
  intro S hS u hu
  have hh := hpos S hS u hu
  have hw : ActualProductTransfer.baseLaw.weight=base := rfl
  simpa only [envelope,ite_eq_right hS.ne_empty,hw] using hh

#print axioms wordOuter_pairedTest
#print axioms envelope_geometryBound
end
end ExceptionalTimes.WordForestGeometry
