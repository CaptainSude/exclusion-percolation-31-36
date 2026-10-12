import ExceptionalTimes.NolinAnnular
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform static collar probabilities from the two published inputs.
The geometric radii and both source-event dictionaries are explicit. -/

namespace ExceptionalTimes.NolinCorridor

open HoleFilling EnvironmentVariance ProbeProduct PairSquareSewing
open Filter
open scoped Classical Topology

theorem exists_wide_ratio (C β : ℝ) (hβ : 0 < β) :
    ∃ K : ℕ, 2 ≤ K ∧ C*(1/(K : ℝ))^β ≤ 1/2 := by
  have ht : Tendsto (fun n : ℕ => C*(n : ℝ)^(-β)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop)
  have he : ∀ᶠ n : ℕ in atTop, C*(n : ℝ)^(-β) < 1/2 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨max N 2,le_max_right _ _,?_⟩
  have h := (hN (max N 2) (le_max_left _ _)).le
  simpa only [one_div,Real.inv_rpow (Nat.cast_nonneg _),Real.rpow_neg (Nat.cast_nonneg _)] using h

theorem rectangle_subset_latticeBox {M n R : ℕ} (hM : M ≤ R) (hn : n ≤ R) :
    rectangle M n ⊆ latticeBox R := by
  intro z hz
  simp only [rectangle,Finset.mem_product,Finset.mem_Icc] at hz
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  omega

theorem uniform_collar_static_bounds
    (hRSW : PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : PublishedAnnularOneArmUpper B₀ C β) (hβ : 0 < β) :
    ∃ K : ℕ, 2 ≤ K ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (r v R : ℕ), 2 ≤ r → B₀ ≤ r → 2*r ≤ v →
        2*K*v ≤ R → R+1 < 64*K*v →
        ∀ D : Finset Site, latticeBox (64*K*R) ⊆ D →
          (c ≤ probability (fairSites D) (fun x => WiredArm (completeColors D x) r (2*K*r+1))) ∧
          (c ≤ probability (fairSites D) (fun x => WiredArm (completeColors D x) v R)) ∧
          (probability (fairSites D) (fun x => WiredArm (completeColors D x) (2*r) (2*K*r)) ≤ 1-c) ∧
          (probability (fairSites D) (fun x => WiredArm (completeColors D x) v (K*v)) ≤ 1-c) := by
  obtain ⟨K,hK,hsmall⟩ := exists_wide_ratio C β hβ
  obtain ⟨δ,hδ,hlower⟩ := wiredArm_lower_of_RSW hRSW (64*K) (by omega)
  let c : ℝ := min δ (1/2)
  have hc : 0 < c := lt_min hδ (by norm_num)
  refine ⟨K,hK,c,hc,?_⟩
  intro r v R hr hBr hrv hvR hRv D hD
  have hKr : r ≤ K*r := Nat.le_mul_of_pos_left r (by omega)
  have hKv : v ≤ K*v := Nat.le_mul_of_pos_left v (by omega)
  have hvpos : 0 < v := by omega
  have hvle : v ≤ R := by nlinarith
  have hrle : r ≤ R := by omega
  have houterD : latticeBox (K*v) ⊆ D :=
    (latticeBox_mono (by nlinarith : K*v ≤ 64*K*R)).trans hD
  have hinnerD : latticeBox (2*K*r) ⊆ D :=
    (latticeBox_mono (by nlinarith : 2*K*r ≤ 64*K*R)).trans hD
  have hcδ : c ≤ δ := min_le_left _ _
  have hcHalf : c ≤ 1/2 := min_le_right _ _
  have h1 := hlower r r (2*K*r+1) hr le_rfl (by nlinarith) (by nlinarith) D
    ((rectangle_subset_latticeBox (by nlinarith : (64*K)*r ≤ 64*K*R)
      (by nlinarith : r ≤ 64*K*R)).trans hD)
  have h2 := hlower v v R (by omega) le_rfl hvle (by nlinarith) D
    ((rectangle_subset_latticeBox (by nlinarith : (64*K)*v ≤ 64*K*R)
      (by nlinarith : v ≤ 64*K*R)).trans hD)
  have h3 := wiredArm_upper_of_published hupper (by omega : B₀ ≤ 2*r)
    (by nlinarith : 2*r < 2*K*r) D hinnerD
  have h4 := wiredArm_upper_of_published hupper (by omega : B₀ ≤ v)
    (by nlinarith : v < K*v) D houterD
  have hKnz : (K : ℝ) ≠ 0 := by positivity
  have hrnz : (r : ℝ) ≠ 0 := by positivity
  have hvnz : (v : ℝ) ≠ 0 := by positivity
  have hratio1 : ((2*r : ℕ) : ℝ) / (2*K*r : ℕ) = 1/(K : ℝ) := by
    push_cast
    field_simp
  have hratio2 : (v : ℝ)/(K*v : ℕ) = 1/(K : ℝ) := by
    push_cast
    field_simp
  rw [hratio1] at h3
  rw [hratio2] at h4
  exact ⟨hcδ.trans h1,hcδ.trans h2,by linarith,by linarith⟩

#print axioms exists_wide_ratio
#print axioms uniform_collar_static_bounds

end ExceptionalTimes.NolinCorridor
