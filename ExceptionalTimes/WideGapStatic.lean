import ExceptionalTimes.WideCollarStatic
import ExceptionalTimes.FairCircuitLaw
import ExceptionalTimes.MixedRadialGap

/-! A uniform static gap bridge, derived from the same literal RSW and
one-arm bounds as the boundary collars. No additional circuit estimate
is assumed. -/

open scoped Classical

namespace ExceptionalTimes.WideGapStatic

open NolinCorridor HoleFilling AnnularCollars FairCircuitLaw
open EnvironmentVariance ProbeProduct PairSquareSewing RadialPivotalRemote

theorem exists_uniform_gap
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : PublishedAnnularOneArmUpper B₀ C β) (hβ : 0<β) :
    ∃ K : ℕ, 2≤K ∧ ∀ J : ℕ, 2≤J → ∃ δ : ℝ, 0<δ ∧
      ∀ n : ℕ, 2≤n → B₀≤n → ∀ D : Finset Site, latticeBox (4*K*J*n) ⊆ D →
        (δ≤probability (fairSites D) (fun x => WiredArm (completeColors D x) n (K*J*n+1))) ∧
        (δ≤probability (fairSites D) (fun x => BlackCircuit (completeColors D x) n (K*n+1))) ∧
        (δ≤probability (fairSites D) (fun x => BlackCircuit (completeColors D x) (J*n) (K*(J*n)+1))) ∧
        (δ^3≤probability (fairSites D)
          (fun x => GapBridge (completeColors D x) n (K*n+1) (J*n) (K*J*n+1))) := by
  obtain ⟨K,hK,hsmall⟩ := exists_wide_ratio C β hβ
  refine ⟨K,hK,?_⟩
  intro J hJ
  obtain ⟨ε,hε,hlower⟩ := wiredArm_lower_of_RSW hRSW (4*K*J) (by nlinarith)
  let δ : ℝ := min ε (1/2)
  have hδ : 0<δ := lt_min hε (by norm_num)
  refine ⟨δ,hδ,?_⟩
  intro n hn hBn D hD
  have hKpos : 0<K := by omega
  have hJpos : 0<J := by omega
  have hnpos : 0<n := by omega
  have hKn : n≤K*n := Nat.le_mul_of_pos_left n hKpos
  have hJn : n≤J*n := Nat.le_mul_of_pos_left n hJpos
  have hJnK : J*n≤K*(J*n) := Nat.le_mul_of_pos_left _ hKpos
  have hmiddle := (min_le_left ε (1/2)).trans (hlower n n (K*J*n+1) hn le_rfl
    (by nlinarith) (by nlinarith) D ((rectangle_subset_latticeBox
      (by omega : (4*K*J)*n≤4*K*J*n) (by nlinarith : n≤4*K*J*n)).trans hD))
  have hupper_at (s : ℕ) (hBs : B₀≤s) (hs : 0<s) (hsD : K*s≤4*K*J*n) :
      probability (fairSites D) (fun x => WiredArm (completeColors D x) s (K*s))≤1/2 := by
    have h := wiredArm_upper_of_published hupper hBs (by nlinarith : s<K*s) D
      ((latticeBox_mono hsD).trans hD)
    have hKnz : (K:ℝ)≠0 := by positivity
    have hsnz : (s:ℝ)≠0 := by positivity
    have hratio : (s:ℝ)/(K*s:ℕ)=1/(K:ℝ) := by push_cast; field_simp
    rw [hratio] at h
    exact h.trans hsmall
  have hcircle_at (s : ℕ) (hBs : B₀≤s) (hs : 0<s)
      (hsD : K*s+1≤4*K*J*n) :
      δ≤probability (fairSites D) (fun x => BlackCircuit (completeColors D x) s (K*s+1)) := by
    rw [circuit_probability_complement boundaryInput D (Nat.le_mul_of_pos_left s hKpos)
      (fun v hv => hD (latticeBox_mono hsD (Finset.mem_sdiff.mp hv).1))]
    have h := hupper_at s hBs hs (by omega)
    have hd : δ≤1/2 := min_le_right _ _
    linarith
  have hcircle1 := hcircle_at n hBn hnpos (by nlinarith)
  have hcircle2 := hcircle_at (J*n) (hBn.trans hJn) (by positivity) (by nlinarith)
  refine ⟨hmiddle,hcircle1,hcircle2,?_⟩
  simp only [probability,FiniteSiteLaw.fairSites_expect_eq_average]
  apply MixedRadialGap.gap_static_lower (completeColors D) (completeColors_monotone D)
    (by nlinarith) hδ.le
  · simpa only [probability,FiniteSiteLaw.fairSites_expect_eq_average] using hmiddle
  · simpa only [probability,FiniteSiteLaw.fairSites_expect_eq_average] using hcircle1
  · simpa only [probability,FiniteSiteLaw.fairSites_expect_eq_average,mul_assoc] using hcircle2

#print axioms exists_uniform_gap

end ExceptionalTimes.WideGapStatic

