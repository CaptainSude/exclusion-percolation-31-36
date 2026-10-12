import ExceptionalTimes.MixedRadialGap
import ExceptionalTimes.MatchingCollarComparison
import ExceptionalTimes.WideGapStatic

open scoped Classical

namespace ExceptionalTimes.MixedGapLaw

universe u v

open DimerLaw FiniteHaar EnvironmentVariance ProbeProduct PairSquareSewing
open HoleFilling AnnularCollars MixedCanonicalLaw MixedAnnularCollar

variable {A O : Type*} [Fintype A] [Fintype O]

theorem average_splitDecode_of_local_cover
    (slot : ((A⊕O)×Fin 2) ↪ Site) (S D : Finset Site) (hSD : S⊆D)
    (hcover : ∀ v∈S, ∃ ie, slot ie=v) (E : Configuration→Prop)
    (hlocal : ∀ ω η, (∀ v∈S, ω v=η v) → (E ω ↔ E η)) :
    average (fun x => indicator (E (splitDecode slot x))) =
      probability (fairSites D) (fun x => E (completeColors D x)) :=
  (FiniteSiteLaw.average_splitDecode_fairSites slot S hcover E hlocal).trans
    (FiniteSiteLaw.fairSites_probability_restrict S D hSD E hlocal).symm

theorem mixed_remote_of_static
    (slot : ((A⊕O)×Fin 2) ↪ Site)
    (p : A→ℝ) (hp0 : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1)
    {r c a b d R : ℕ} (hrc : r≤c) (hca : c≤a) (had : a≤d)
    (hrb : r≤b) (hbd : b≤d) (hdR : d≤R)
    (D : Finset Site) (hD : annularSites r R⊆D)
    (hcover : ∀ v∈annularSites r R, ∃ ie, slot ie=v)
    {δ : ℝ} (hδ : 0<δ)
    (hmiddle : δ≤probability (fairSites D) (fun x => WiredArm (completeColors D x) c d))
    (hcircle1 : δ≤probability (fairSites D) (fun x => BlackCircuit (completeColors D x) c a))
    (hcircle2 : δ≤probability (fairSites D) (fun x => BlackCircuit (completeColors D x) b d)) :
    mixedProbability p (fun x => WiredArm (splitDecode slot x) r a)*
      mixedProbability p (fun x => WiredArm (splitDecode slot x) b R) ≤
        mixedProbability p (fun x => WiredArm (splitDecode slot x) r R)/δ^6 := by
  apply MixedRadialGap.mixed_remote_comparison (splitDecode slot) (splitDecode_monotone slot)
    p hp0 hp1 hrc hca had hrb hbd hdR hδ
  · rw [average_splitDecode_of_local_cover slot (annularSites r R) D hD hcover
      (fun ω => WiredArm ω c d) (fun ω η he => wiredArm_congr_on_annulus ω η
        (hca.trans had) (fun v hv hi => he v (annularSites_mono hrc hdR
          (Finset.mem_sdiff.mpr ⟨hv,hi⟩))))]
    exact hmiddle
  · rw [average_splitDecode_of_local_cover slot (annularSites r R) D hD hcover
      (fun ω => BlackCircuit ω c a) (fun ω η he => blackCircuit_congr (fun v hv hi =>
        he v (Finset.mem_sdiff.mpr ⟨latticeBox_mono (by omega) hv,
          fun h => hi (latticeBox_mono hrc h)⟩)))]
    exact hcircle1
  · rw [average_splitDecode_of_local_cover slot (annularSites r R) D hD hcover
      (fun ω => BlackCircuit ω b d) (fun ω η he => blackCircuit_congr (fun v hv hi =>
        he v (Finset.mem_sdiff.mpr ⟨latticeBox_mono (by omega) hv,
          fun h => hi (latticeBox_mono hrb h)⟩)))]
    exact hcircle2

/-- Uniform two-time remote-factor gluing from the already stated static
published inputs. It holds for every injective finite dimer enumeration,
every active/exterior split and every valid set of refresh probabilities. -/
theorem exists_uniform_mixed_gap
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0<β) :
    ∃ K : ℕ, 2≤K ∧ ∀ J : ℕ, 2≤J → ∃ δ : ℝ, 0<δ ∧
      ∀ n r R : ℕ, 2≤n → B₀≤n → r≤n → K*J*n+1≤R →
        ∀ {A : Type u} {O : Type v} [Fintype A] [Fintype O]
          (slot : ((A⊕O)×Fin 2) ↪ Site),
          (∀ v∈annularSites r R, ∃ ie, slot ie=v) →
          ∀ p : A→ℝ, (∀ i, 0≤p i) → (∀ i, p i≤1) →
            mixedProbability p (fun x => WiredArm (splitDecode slot x) r (K*n+1))*
              mixedProbability p (fun x => WiredArm (splitDecode slot x) (J*n) R) ≤
                mixedProbability p (fun x => WiredArm (splitDecode slot x) r R)/δ^6 := by
  obtain ⟨K,hK,hJ⟩ := WideGapStatic.exists_uniform_gap boundaryInput hRSW hupper hβ
  refine ⟨K,hK,?_⟩
  intro J hJ2
  obtain ⟨δ,hδ,hstatic⟩ := hJ J hJ2
  refine ⟨δ,hδ,?_⟩
  intro n r R hn hBn hrn hdR A O instA instO slot hcover p hp0 hp1
  let D := latticeBox (max (R+1) (4*K*J*n))
  obtain ⟨hmiddle,hcircle1,hcircle2,_⟩ := hstatic n hn hBn D
    (latticeBox_mono (le_max_right _ _))
  have hKn : n≤K*n := Nat.le_mul_of_pos_left n (by omega)
  have hJn : n≤J*n := Nat.le_mul_of_pos_left n (by omega)
  have hKJn : J*n≤K*(J*n) := Nat.le_mul_of_pos_left _ (by omega)
  have hKnJn := Nat.mul_le_mul_left K hJn
  apply mixed_remote_of_static slot p hp0 hp1 hrn (by omega)
    (by simpa only [mul_assoc] using Nat.add_le_add_right hKnJn 1)
    (hrn.trans hJn) (by simpa only [mul_assoc] using hKJn.trans (Nat.le_succ _)) hdR
    D (fun v hv => latticeBox_mono (le_max_left _ _) (Finset.mem_sdiff.mp hv).1)
    hcover hδ hmiddle hcircle1
  simpa only [mul_assoc] using hcircle2

#print axioms mixed_remote_of_static
#print axioms exists_uniform_mixed_gap

end ExceptionalTimes.MixedGapLaw
