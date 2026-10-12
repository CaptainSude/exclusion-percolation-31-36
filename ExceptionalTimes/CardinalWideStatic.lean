import ExceptionalTimes.CardinalWideGuards
import ExceptionalTimes.CardinalRSWBridge
import ExceptionalTimes.WideGapStatic

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open Annulus AnnularCollars NolinCorridor HoleFilling FairCircuitLaw
open EnvironmentVariance FiniteHaar ProbeProduct

def ColoredGuard (c : Site) (w U : ℕ) (color : Bool) (ω : Configuration) : Prop :=
  ∃ C : SurroundingCircuit w U, ∀ z ∈ (shiftedCircuit c C).support, ω z=color

/-- Exact transport of an ordinary black-circuit lower bound to a
translated guard of either color in the original finite site law. -/
theorem coloredGuard_probability_lower {Λ : Finset Site} (c : Site) (w U : ℕ)
    (hΛ : ∀ z ∈ latticeBox U, c+z ∈ Λ) (color : Bool) (δ : ℝ)
    (hlower : δ ≤ probability (fairSites ↥(latticeBox U))
      (fun ω => BlackCircuit (completeColors (latticeBox U) ω) w U)) :
    δ ≤ probability (fairSites ↥Λ) (fun ω => ColoredGuard c w U color (complete ω)) := by
  let D := latticeBox U
  let select : D ↪ Λ :=
    ⟨fun z => ⟨c+z,hΛ z z.property⟩,by
      intro a b hab
      apply Subtype.ext
      exact add_left_cancel (congrArg Subtype.val hab)⟩
  let restrict (ω : Λ → Bool) : D → Bool :=
    fun z => if color then ω (select z) else !(ω (select z))
  let E (ω : D → Bool) := BlackCircuit (completeColors D ω) w U
  have hprob : probability (fairSites ↥Λ) (fun ω => E (restrict ω)) =
      probability (fairSites ↥D) E := by
    simp only [probability,FiniteSiteLaw.fairSites_expect_eq_average]
    exact average_favorable_restrict select color (fun ω => indicator (E ω))
  have hlow : δ ≤ probability (fairSites ↥Λ) (fun ω => E (restrict ω)) := by
    rw [hprob]
    exact hlower
  apply hlow.trans (CanonicalRadialLaw.probability_mono _ ?_)
  intro ω hω
  obtain ⟨C,hC⟩ := hω
  refine ⟨C,?_⟩
  intro z hz
  rw [shiftedCircuit,SimpleGraph.Walk.support_map] at hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  have hvD : v ∈ D := C.inside v hv
  have hvΛ := hΛ v hvD
  have hcol := hC v hv
  change complete ω (c+v)=color
  simp only [completeColors,dite_eq_left hvD] at hcol
  change (if color then ω ⟨c+v,hvΛ⟩ else !(ω ⟨c+v,hvΛ⟩))=true at hcol
  simp only [complete,dite_eq_left hvΛ]
  cases color <;> simpa using hcol

/-- The source's actual one-arm upper estimate and planar circuit
duality supply a uniformly positive guard probability at one sufficiently
wide fixed ratio. A ratio-two circuit lower bound is not assumed. -/
theorem coloredGuard_lower_of_published
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    {B₀ : ℕ} {C β : ℝ} (hupper : PublishedAnnularOneArmUpper B₀ C β) (hβ : 0 < β) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ w : ℕ, 1 ≤ w → B₀ ≤ w →
      ∀ (c : Site) (Λ : Finset Site),
        (∀ z ∈ latticeBox (K*w+1), c+z ∈ Λ) → ∀ color : Bool,
          (1/2:ℝ) ≤ probability (fairSites ↥Λ)
            (fun ω => ColoredGuard c w (K*w+1) color (complete ω)) := by
  obtain ⟨K,hK,hsmall⟩ := exists_wide_ratio C β hβ
  refine ⟨K,hK,?_⟩
  intro w hw hBw c Λ hΛ color
  apply coloredGuard_probability_lower c w (K*w+1) hΛ color (1/2)
  have hKw : w ≤ K*w := Nat.le_mul_of_pos_left w (by omega)
  rw [circuit_probability_complement boundaryInput (latticeBox (K*w+1)) hKw
    (fun z hz => latticeBox_mono (by omega) (Finset.mem_sdiff.mp hz).1)]
  have hbound := wiredArm_upper_of_published hupper hBw (by nlinarith : w<K*w)
    (latticeBox (K*w+1)) (latticeBox_mono (by omega))
  have hKnz : (K:ℝ) ≠ 0 := by positivity
  have hwnz : (w:ℝ) ≠ 0 := by positivity
  have hratio : (w:ℝ)/(K*w:ℕ)=1/(K:ℝ) := by push_cast; field_simp
  rw [hratio] at hbound
  linarith

#print axioms coloredGuard_probability_lower
#print axioms coloredGuard_lower_of_published

end ExceptionalTimes.PairSquareSewing
