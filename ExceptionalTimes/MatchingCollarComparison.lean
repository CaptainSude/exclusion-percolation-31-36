import ExceptionalTimes.ActiveWideLaw
import ExceptionalTimes.FiniteSiteLaw
import ExceptionalTimes.FairSiteRestriction
import ExceptionalTimes.WideCollarStatic
import ExceptionalTimes.WideCollarRadii

/-! The actual finite matching collar comparison, with constants obtained
solely from the literal published static inputs. The finite matching and
its active support are constructed, and no dynamical estimate is assumed. -/

open scoped Classical

namespace ExceptionalTimes.MatchingCollarComparison

noncomputable section

open DimerLaw ManyDimerLaw FiniteHaar EnvironmentVariance ProbeProduct PairSquareSewing
open HoleFilling ActiveMiddlePartition ActivePartitionLaw MixedAnnularCollar MixedCanonicalLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance {A O : Type*} : DecidableEq (A ⊕ O) :=
  fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ActiveLabels slot z S) := fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ExteriorLabels slot z S) := fun a b => Classical.propDecidable (a = b)

theorem average_wiredArm {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (D : Finset Site) {r R : ℕ} (hrR : r ≤ R)
    (hD : annularSites r R ⊆ D) (hcover : ∀ x ∈ D, ∃ b, slot b = x) :
    average (fun x => indicator (WiredArm (pairDecode slot x) r R)) =
      probability (fairSites D) (fun x => WiredArm (completeColors D x) r R) :=
  FiniteSiteLaw.average_pairDecode_fairSites slot D hcover _ (fun ω η he =>
    wiredArm_congr_on_annulus ω η hrR
      (fun x hx hi => he x (hD (Finset.mem_sdiff.mpr ⟨hx,hi⟩))))

/-- Large iid source domains may be used for a static estimate without
enlarging the original matching: only the literal arm support is needed
in the slot. -/
theorem average_wiredArm_of_local_cover {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (D : Finset Site) {r R : ℕ} (hrR : r ≤ R)
    (hD : annularSites r R ⊆ D)
    (hcover : ∀ x ∈ annularSites r R, ∃ b, slot b = x) :
    average (fun x => indicator (WiredArm (pairDecode slot x) r R)) =
      probability (fairSites D) (fun x => WiredArm (completeColors D x) r R) := by
  apply (average_wiredArm slot (annularSites r R) hrR (fun _ hx => hx) hcover).trans
  symm
  exact FiniteSiteLaw.fairSites_probability_restrict (annularSites r R) D hD
    (fun ω => WiredArm ω r R) (fun ω η he => wiredArm_congr_on_annulus ω η hrR
      (fun x hx hi => he x (Finset.mem_sdiff.mpr ⟨hx,hi⟩)))

theorem collar_of_static_fairSites {B : Type*} [Fintype B]
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    {r s u v w t R : ℕ}
    (hrs : r ≤ s) (hsu : s ≤ u) (hut : u+1 ≤ t)
    (hrv : r ≤ v) (hvw : v ≤ w) (hwt : w+1 ≤ t) (htR : t ≤ R)
    (D : Finset Site) (hD : annularSites r R ⊆ D)
    (hcover : ∀ x ∈ annularSites r R, ∃ b, slot b = x) {c : ℝ} (hc : 0 < c)
    (hinner : c ≤ probability (fairSites D) (fun x => WiredArm (completeColors D x) r (u+1)))
    (houter : c ≤ probability (fairSites D) (fun x => WiredArm (completeColors D x) v R))
    (hcircle1 : probability (fairSites D) (fun x => WiredArm (completeColors D x) s u) ≤ 1-c)
    (hcircle2 : probability (fairSites D) (fun x => WiredArm (completeColors D x) v w) ≤ 1-c) :
    manyProbability p (fun x => WiredArm (pairDecode slot x) r R) ≤
      mixedProbability (fun a : ActiveLabels slot z (annularSites s t) => p a.val)
        (fun x => WiredArm (splitDecode (splitSlot slot z (annularSites s t)) x) r R) / c^8 := by
  apply partition_wide_collar_comparison boundaryInput slot z hz0 hp p hp0 hp1
    hrs hsu hut hrv hvw hwt htR hcover hc
  · rw [average_wiredArm_of_local_cover slot D (by omega)
      ((annularSites_mono le_rfl (by omega)).trans hD)
      (fun x hx => hcover x (annularSites_mono le_rfl (by omega) hx))]
    exact hinner
  · rw [average_wiredArm_of_local_cover slot D (by omega)
      ((annularSites_mono hrv le_rfl).trans hD)
      (fun x hx => hcover x (annularSites_mono hrv le_rfl hx))]
    exact houter
  · rw [average_wiredArm_of_local_cover slot D hsu ((annularSites_mono hrs (by omega)).trans hD)
      (fun x hx => hcover x (annularSites_mono hrs (by omega) hx))]
    exact hcircle1
  · rw [average_wiredArm_of_local_cover slot D hvw ((annularSites_mono hrv (by omega)).trans hD)
      (fun x hx => hcover x (annularSites_mono hrv (by omega) hx))]
    exact hcircle2

/-- Uniform collar constants come from published rectangle RSW and the
published static annular one-arm upper bound. At each scale the actual
finite matching is enumerated and the active middle labels are selected.
The result is a genuine full matching-law to mixed-law comparison. -/
theorem exists_uniform_matching_collar
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0 < β) :
    ∃ K : ℕ, 2 ≤ K ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (z : Site), z ≠ (0,0) → ∀ (r R : ℕ), 2 ≤ r → B₀ ≤ r → 32*K*r ≤ R →
        ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ Site,
          (∀ x, x ∈ FiniteMatchingClosure.closure (PeriodicMatching.partner z)
            (latticeBox (R+1)) ↔ ∃ b, slot b = x) ∧
          (∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0))) ∧
          ∀ (p : Fin k → ℝ), (∀ b, 0 ≤ p b) → (∀ b, p b ≤ 1) →
            manyProbability p (fun x => WiredArm (pairDecode slot x) r R) ≤
              mixedProbability
                (fun a : ActiveLabels slot z
                  (annularSites (2*r) (2*K*WideCollarRadii.outerStart K R)) => p a.val)
                (fun x => WiredArm (splitDecode
                  (splitSlot slot z (annularSites (2*r) (2*K*WideCollarRadii.outerStart K R))) x)
                  r R) / c^8 := by
  obtain ⟨K,hK,c,hc,hstatic⟩ := NolinCorridor.uniform_collar_static_bounds hRSW hupper hβ
  refine ⟨K,hK,c,hc,?_⟩
  intro z hz0 r R hr hBr hR
  obtain ⟨k,slot,hcover,hp⟩ := FiniteMatchingClosure.periodic_closure_enumeration z hz0
    (latticeBox (R+1))
  refine ⟨k,slot,hcover,hp,?_⟩
  intro p hp0 hp1
  obtain ⟨hrv,hrs,hsu,hut,hrv',hvw,hwt,htR,_,hRv⟩ :=
    WideCollarRadii.chosen_radii hK hr hR
  obtain ⟨hinner,houter,hcircle1,hcircle2⟩ := hstatic r (WideCollarRadii.outerStart K R) R
    hr hBr hrv htR hRv (latticeBox (64*K*R)) (fun _ hx => hx)
  apply collar_of_static_fairSites boundaryInput slot z hz0 hp p hp0 hp1
    hrs hsu hut hrv' hvw hwt htR (latticeBox (64*K*R)) _ _ hc hinner houter hcircle1 hcircle2
  · intro x hx
    apply latticeBox_mono _ (Finset.mem_sdiff.mp hx).1
    nlinarith
  · intro x hx
    exact (hcover x).mp (FiniteMatchingClosure.subset_closure _ _ (Finset.mem_sdiff.mp hx).1)

#print axioms average_wiredArm
#print axioms average_wiredArm_of_local_cover
#print axioms collar_of_static_fairSites
#print axioms exists_uniform_matching_collar

end

end ExceptionalTimes.MatchingCollarComparison
