import ExceptionalTimes.CanonicalHexAnnuli
import ExceptionalTimes.GeometricAnnulusScales

/-! Uniform circular paired-arm decay from a single fixed-aspect
reference-time estimate. All subannuli, their whole-dimer separation,
necessary events, time comparison and power summation are proved.

The fixed-aspect input is explicitly the remaining dynamical mixing
obligation; it is not declared to be a published canonical theorem. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.CanonicalAnnularDecay

open Annulus PairSquareSewing CanonicalScaleProduct CanonicalHexAnnuli
open GeometricAnnulusScales ActivePartitionLaw CanonicalRadialLaw ManyDimerLaw DimerLaw

variable {B : Type*} [Fintype B]

theorem circular_decay_of_fixed_aspect (orderInput : PublishedAnnularCrosscutOrder)
    (slot : B×Fin 2 ↪ Site) (z : Site) {d : ℕ} (hz : z∈latticeBox d)
    (hpartner : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (P : Probe) (M m : ℕ) (hM : 2≤M) (hd : 2*d<m)
    (hinner : 4*P.innerRadius≤P.mesh*(m:ℝ))
    (reference : ℕ → ℝ) (t a : ℝ) (ha : 0≤a)
    (href0 : ∀ s,m≤s → 0≤reference s)
    (href : ∀ s,m≤s → reference s≤t)
    (hfixed : ∀ s,m≤s →
      manyProbability (fun _ => refreshProbability (reference s))
        (fun ω => HexFourArms P.center (s:ℤ) ((M*s:ℕ):ℤ) (pairDecode slot ω))≤
          (2*(M:ℝ))^(-a)) :
    manyProbability (fun _ => refreshProbability t)
      (fun ω => FourArms P (pairDecode slot ω))≤
        (2*(M:ℝ))^a*(2*P.mesh*(m:ℝ)/P.outerRadius)^a := by
  have hm : 0<m := by omega
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have hM1 : 1≤M := by omega
  have hΛ : 1<2*(M:ℝ) := by exact_mod_cast (show 1<2*M by omega)
  have ht : 0≤t := (href0 m le_rfl).trans (href m le_rfl)
  have hP : 0<P.outerRadius := by linarith [P.inner_pos,P.radii]
  have hmesh : 0<P.mesh := P.mesh_pos
  let R : ℝ := P.outerRadius/(2*P.mesh)
  have hR : 0<R := div_pos hP (by positivity)
  have heq : (m:ℝ)/R=2*P.mesh*(m:ℝ)/P.outerRadius := by
    dsimp [R]
    field_simp
  rw [←heq]
  by_cases hlarge : (m:ℝ)≤R
  · obtain ⟨N,hlo,hhi⟩ := exists_annulus_count hΛ hm' hlarge
    let inner : Fin N → ℤ := fun i => (scale M m i.val:ℤ)
    let outer : Fin N → ℤ := fun i => (M*scale M m i.val:ℕ)
    have hbase (i : Fin N) : m≤scale M m i.val := base_le_scale hM1 i.val
    have hpositive (i : Fin N) : 0<scale M m i.val := hm.trans_le (hbase i)
    have hir (i : Fin N) : 0 < inner i := by
      dsimp only [inner]
      exact_mod_cast hpositive i
    have hior (i : Fin N) : inner i < outer i := by
      dsimp [inner,outer]
      exact_mod_cast (show scale M m i.val<M*scale M m i.val by nlinarith [hpositive i])
    have hgaps (i j : Fin N) (hij : i<j) : outer i+2*(d:ℤ) < inner j := by
      dsimp only [inner,outer]
      exact_mod_cast gap hM1 hd hij
    have hins (i : Fin N) : 4*P.innerRadius≤P.mesh*(inner i:ℝ) := by
      have hcast : (m:ℝ)≤(inner i:ℝ) := by
        dsimp only [inner]
        exact_mod_cast hbase i
      exact hinner.trans (mul_le_mul_of_nonneg_left hcast P.mesh_pos.le)
    have houts (i : Fin N) : 2*P.mesh*(outer i:ℝ)≤P.outerRadius := by
      have hs : (outer i:ℝ)≤(scale M m N:ℝ) := by
        dsimp only [outer]
        exact_mod_cast outer_le_last (m := m) hM1 i.isLt
      have hlast : (scale M m N:ℝ)≤R := by rwa [scale_real]
      have h := hs.trans hlast
      dsimp [R] at h
      have H := (le_div_iff₀ (by positivity : (0:ℝ)<2*P.mesh)).mp h
      nlinarith
    have hq := circular_probability_le_power orderInput N slot z hz hpartner P inner outer
      hir hior hgaps hins houts (fun i => reference (scale M m i.val)) t ht
      (fun i => href0 _ (hbase i)) (fun i => href _ (hbase i)) ((2*(M:ℝ))^(-a))
      (fun i => hfixed _ (hbase i))
    exact probability_power_le hΛ ha hm' hR N ((div_lt_iff₀ hm').mpr hhi).le hq
  · have hratio : 1≤(m:ℝ)/R := (le_div_iff₀ hR).mpr (by linarith)
    have hp := Real.one_le_rpow hratio ha
    have hbase := Real.one_le_rpow hΛ.le ha
    have hprod : 1≤(2*(M:ℝ))^a*((m:ℝ)/R)^a := by nlinarith
    exact (many_le_one _ (fun _ => refreshProbability_nonneg ht)
      (fun _ => refreshProbability_le_one t) _).trans hprod

#print axioms circular_decay_of_fixed_aspect

end ExceptionalTimes.CanonicalAnnularDecay
