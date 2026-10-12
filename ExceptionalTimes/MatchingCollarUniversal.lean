import ExceptionalTimes.MatchingCollarComparison

/-! Uniform collar comparison for every finite matching enumeration.
The constants are independent of the label type, support enumeration,
matching displacement, radii, and individual block parameters. -/

open scoped Classical

namespace ExceptionalTimes.MatchingCollarComparison

noncomputable section

open DimerLaw ManyDimerLaw HoleFilling ActiveMiddlePartition ActivePartitionLaw
open MixedAnnularCollar MixedCanonicalLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance {A O : Type*} : DecidableEq (A ⊕ O) :=
  fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ActiveLabels slot z S) := fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ExteriorLabels slot z S) := fun a b => Classical.propDecidable (a = b)

universe u

/-- Any enumeration covering the literal arm support admits the same
published-input collar constants and the explicitly selected middle. -/
theorem uniform_matching_collar
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0 < β) :
    ∃ K : ℕ, 2 ≤ K ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (z : Site), z ≠ (0,0) → ∀ (r R : ℕ), 2 ≤ r → B₀ ≤ r → 32*K*r ≤ R →
        ∀ {B : Type u} [Fintype B] (slot : B × Fin 2 ↪ Site),
          (∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0))) →
          (∀ x ∈ annularSites r R, ∃ b, slot b = x) →
          ∀ (p : B → ℝ), (∀ b, 0 ≤ p b) → (∀ b, p b ≤ 1) →
            manyProbability p (fun x => WiredArm (pairDecode slot x) r R) ≤
              mixedProbability
                (fun a : ActiveLabels slot z
                  (annularSites (2*r) (2*K*WideCollarRadii.outerStart K R)) => p a.val)
                (fun x => WiredArm (splitDecode
                  (splitSlot slot z (annularSites (2*r) (2*K*WideCollarRadii.outerStart K R))) x)
                  r R) / c^8 := by
  obtain ⟨K,hK,c,hc,hstatic⟩ := NolinCorridor.uniform_collar_static_bounds hRSW hupper hβ
  refine ⟨K,hK,c,hc,?_⟩
  intro z hz0 r R hr hBr hR B inst slot hp hcover p hp0 hp1
  obtain ⟨hrv,hrs,hsu,hut,hrv',hvw,hwt,htR,_,hRv⟩ :=
    WideCollarRadii.chosen_radii hK hr hR
  obtain ⟨hinner,houter,hcircle1,hcircle2⟩ := hstatic r (WideCollarRadii.outerStart K R) R
    hr hBr hrv htR hRv (latticeBox (64*K*R)) (fun _ hx => hx)
  apply collar_of_static_fairSites boundaryInput slot z hz0 hp p hp0 hp1
    hrs hsu hut hrv' hvw hwt htR (latticeBox (64*K*R)) _ hcover
    hc hinner houter hcircle1 hcircle2
  intro x hx
  apply latticeBox_mono _ (Finset.mem_sdiff.mp hx).1
  nlinarith

#print axioms uniform_matching_collar

end

end ExceptionalTimes.MatchingCollarComparison
