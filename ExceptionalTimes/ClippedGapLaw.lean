import ExceptionalTimes.ClippedRadialGap
import ExceptionalTimes.MixedGapLaw

open scoped Classical
open Set

namespace ExceptionalTimes.ClippedGapLaw

universe u v

open DimerLaw FiniteHaar EnvironmentVariance ProbeProduct PairSquareSewing
open HoleFilling AnnularCollars ClippedRadialGap MixedCanonicalLaw MixedAnnularCollar

variable {A O : Type*} [Fintype A] [Fintype O]

theorem mixed_remote_comparison
    (decode : ((A→Color)×(O→Color))→Configuration) (hdecode : Monotone decode)
    (p : A→ℝ) (hp0 : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1)
    {r c a b d R : ℕ} (hrR : r≤R) (hca : c≤a) (haR : a≤R)
    (had : a≤d) (hrb : r≤b) (hbd : b≤d)
    {ε : ℝ} (hε : 0<ε)
    (hstatic : ε≤average (fun x => indicator (Bridge (decode x) r c a b d R))) :
    mixedProbability p (fun x => InnerRemote (decode x) r c a)*
      mixedProbability p (fun x => OuterRemote (decode x) b d R) ≤
        mixedProbability p (fun x => WiredArm (decode x) r R)/ε^2 := by
  let E : Set ((A→Color)×(O→Color)) := {x | InnerRemote (decode x) r c a}
  let F : Set ((A→Color)×(O→Color)) := {x | OuterRemote (decode x) b d R}
  let H : Set ((A→Color)×(O→Color)) := {x | Bridge (decode x) r c a b d R}
  have hE : IsUpperSet E := fun _ _ hxy h => innerRemote_mono (hdecode hxy) hca h
  have hF : IsUpperSet F := fun _ _ hxy h => outerRemote_mono (hdecode hxy) hbd h
  have hH : IsUpperSet H := fun _ _ hxy h => bridge_mono (hdecode hxy)
    (bridge_radii hrR hca haR had hrb hbd) h
  have hEF : IsUpperSet (E∩F) := fun _ _ hxy h => ⟨hE hxy h.1,hF hxy h.2⟩
  have hpair := mixed_event_association p hp0 hp1 E F hE hF
  have hassoc := mixed_event_association p hp0 hp1 (E∩F) H hEF hH
  have hmono := mixedProbability_mono p hp0 hp1
    (fun x => x∈(E∩F)∩H) (fun x => WiredArm (decode x) r R)
    (fun x h => remote_and_bridge_implies_arm (decode x) hrR hca haR had hrb hbd h.1.1 h.1.2 h.2)
  have hsquare := mixed_event_square_lower p hp0 hp1 (fun x => x∈H)
  have hbridge : ε^2≤mixedProbability p (fun x => x∈H) :=
    (pow_le_pow_left₀ hε.le hstatic 2).trans hsquare
  have hprod := mul_le_mul hpair hbridge (sq_nonneg ε)
    (mixedProbability_nonneg p hp0 hp1 (fun x => x∈E∩F))
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  exact hprod.trans (hassoc.trans hmono)

/-- All endpoint regimes are covered. If the local gap reaches an endpoint
of the radial annulus, the corresponding remote event is exactly True.
The original finite dimer domain need cover only the radial support. -/
theorem exists_uniform_clipped_mixed_gap
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0<β) :
    ∃ K : ℕ, 2≤K ∧ ∀ J : ℕ, 2≤J → ∃ δ : ℝ, 0<δ ∧
      ∀ n r R : ℕ, 2≤n → B₀≤n → r≤R → r≤J*n → K*n+1≤R →
        ∀ {A : Type u} {O : Type v} [Fintype A] [Fintype O]
          (slot : ((A⊕O)×Fin 2) ↪ Site),
          (∀ v∈annularSites r R, ∃ ie, slot ie=v) →
          ∀ p : A→ℝ, (∀ i, 0≤p i) → (∀ i, p i≤1) →
            mixedProbability p (fun x => InnerRemote (splitDecode slot x) r n (K*n+1))*
              mixedProbability p (fun x => OuterRemote (splitDecode slot x) (J*n) (K*J*n+1) R) ≤
                mixedProbability p (fun x => WiredArm (splitDecode slot x) r R)/δ^6 := by
  obtain ⟨K,hK,hJ⟩ := WideGapStatic.exists_uniform_gap boundaryInput hRSW hupper hβ
  refine ⟨K,hK,?_⟩
  intro J hJ2
  obtain ⟨δ,hδ,hstatic⟩ := hJ J hJ2
  refine ⟨δ,hδ,?_⟩
  intro n r R hn hBn hrR hrb haR A O instA instO slot hcover p hp0 hp1
  let D := latticeBox (max (R+1) (4*K*J*n))
  have hs := (hstatic n hn hBn D (latticeBox_mono (le_max_right _ _))).2.2.2
  have hKn : n≤K*n := Nat.le_mul_of_pos_left n (by omega)
  have hJn : n≤J*n := Nat.le_mul_of_pos_left n (by omega)
  have hKJn : J*n≤K*(J*n) := Nat.le_mul_of_pos_left _ (by omega)
  have had : K*n+1≤K*J*n+1 := by
    simpa only [mul_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_left K hJn) 1
  have hbd : J*n≤K*J*n+1 := by simpa only [mul_assoc] using hKJn.trans (Nat.le_succ _)
  have hmid := bridge_radii hrR (hKn.trans (Nat.le_succ _)) haR had hrb hbd
  have hb : δ^3≤average (fun x => indicator
      (Bridge (splitDecode slot x) r n (K*n+1) (J*n) (K*J*n+1) R)) := by
    rw [MixedGapLaw.average_splitDecode_of_local_cover slot (annularSites r R) D
      (fun v hv => latticeBox_mono (le_max_left _ _) (Finset.mem_sdiff.mp hv).1) hcover
      (fun ω => Bridge ω r n (K*n+1) (J*n) (K*J*n+1) R)
      (fun _ _ he => bridge_locality hrR (hKn.trans (Nat.le_succ _)) haR had hrb hbd he)]
    exact hs.trans (CanonicalRadialLaw.probability_mono _
      (fun x h => gap_implies_bridge (completeColors D x) hmid h))
  have h := mixed_remote_comparison (splitDecode slot) (splitDecode_monotone slot)
    p hp0 hp1 hrR (hKn.trans (Nat.le_succ _)) haR had hrb hbd (pow_pos hδ 3) hb
  have he : (δ^3)^2=δ^6 := by ring
  simpa only [he] using h

#print axioms exists_uniform_clipped_mixed_gap

end ExceptionalTimes.ClippedGapLaw
