import ExceptionalTimes.CanonicalProbeDecay
import ExceptionalTimes.CanonicalHexAnnuli
import ExceptionalTimes.GeometricAnnulusScales

/-! Uniform circular paired-arm decay from a single fixed-aspect
reference-time estimate. All subannuli, their whole-dimer separation,
necessary events, time comparison and power summation are proved.

The fixed-aspect input is explicitly the remaining dynamical mixing
obligation; it is not declared to be a published canonical theorem. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.SampledProbeDecay

open Annulus PairSquareSewing CanonicalScaleProduct CanonicalHexAnnuli
open GeometricAnnulusScales ActivePartitionLaw CanonicalRadialLaw ManyDimerLaw DimerLaw

variable {B : Type*} [Fintype B]

theorem circular_decay_of_sampled_fixed_aspect (orderInput : PublishedAnnularCrosscutOrder)
    (slot : B×Fin 2 ↪ Site) (z : Site) {d : ℕ} (hz : z∈latticeBox d)
    (hpartner : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (P : Probe) (M m : ℕ) (hM : 2≤M) (hd : 2*d<m)
    (hinner : 4*P.innerRadius≤P.mesh*(m:ℝ))
    (reference : ℕ → ℝ) (t a : ℝ) (ha : 0≤a)
    (href0 : ∀ s,m≤s → 0≤reference s)
    (href : ∀ s,m≤s → reference s≤t)
    (hfixed : ∀ i, let s := scale M m i
      2*P.mesh*(M*s:ℕ)≤P.outerRadius →
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
      (fun i => hfixed i.val (by simpa only [outer,Int.cast_natCast] using houts i))
    exact probability_power_le hΛ ha hm' hR N ((div_lt_iff₀ hm').mpr hhi).le hq
  · have hratio : 1≤(m:ℝ)/R := (le_div_iff₀ hR).mpr (by linarith)
    have hp := Real.one_le_rpow hratio ha
    have hbase := Real.one_le_rpow hΛ.le ha
    have hprod : 1≤(2*(M:ℝ))^a*((m:ℝ)/R)^a := by nlinarith
    exact (many_le_one _ (fun _ => refreshProbability_nonneg ht)
      (fun _ => refreshProbability_le_one t) _).trans hprod

#print axioms circular_decay_of_sampled_fixed_aspect

open RadialFourArmProbe RadialMixedAbsorption

theorem hex_region_subset_probe (P : Probe) (s S : ℕ)
    (hinner : 4*P.innerRadius≤P.mesh*(s : ℝ))
    (houter : 2*P.mesh*(S : ℝ)≤P.outerRadius) :
    CanonicalHexAnnuli.region P.center (s : ℤ) (S : ℤ) ⊆ P.region := by
  intro v hv
  obtain ⟨hlo,hhi⟩ := P.hexRadius_comparison v
  have hvlo : (s : ℝ)≤(Annulus.hexRadius (v-P.center) : ℝ) := by exact_mod_cast hv.1
  have hvhi : (Annulus.hexRadius (v-P.center) : ℝ)≤(S : ℝ) := by exact_mod_cast hv.2
  have hl := mul_le_mul_of_nonneg_left hvlo P.mesh_pos.le
  have hh := mul_le_mul_of_nonneg_left hvhi P.mesh_pos.le
  change P.innerRadius/2≤P.radius v ∧ P.radius v≤2*P.outerRadius
  constructor <;> nlinarith [P.inner_pos,P.radii]

/-- Fixed-aspect bounds are needed only where the actual finite matching
covers the entire tested hex annulus. The artificial exterior of the
decoder is therefore not used to infer a probability bound. -/
theorem probe_decay_of_sampled_fixed_aspect (orderInput : PublishedAnnularCrosscutOrder)
    (slot : B×Fin 2 ↪ Site) (z : Site) (K m d M : ℕ)
    (hK : 2≤K) (hm : 0<m) (hd : d≤m) (hM : 2≤M) (hz : z∈latticeBox d)
    (hpartner : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (reference : ℕ→ℝ) (t h : ℝ) (hh : 0<h)
    (href0 : ∀ s,256*m≤s → 0≤reference s)
    (href : ∀ s,256*m≤s → reference s≤t)
    (hfixed : ∀ x s,(∃ i,s=scale M (256*m) i) →
      (∀ v∈CanonicalHexAnnuli.region x (s : ℤ) ((M*s : ℕ) : ℤ),∃ b,slot b=v) →
      manyProbability (fun _ => refreshProbability (reference s))
        (fun ω => HexFourArms x (s : ℤ) ((M*s : ℕ) : ℤ) (pairDecode slot ω)) ≤
          (2*(M : ℝ))^(-(2+h))) :
    NewPairedProbeDecay slot K m d hK hm hd (refreshProbability t)
      ( (2*(M : ℝ)*32768)^(2+h)) h := by
  intro x hscale hcover
  let P := probe x K m d hK hm hd hscale
  have hinner : 4*P.innerRadius≤P.mesh*(256*m : ℕ) := by
    dsimp only [P,probe]
    have hd' : (d : ℝ)≤m := by exact_mod_cast hd
    have hm' : (1 : ℝ)≤m := by exact_mod_cast hm
    push_cast
    nlinarith
  have hdecay := circular_decay_of_sampled_fixed_aspect orderInput slot z hz hpartner
    P M (256*m) hM (by omega) hinner reference t (2+h) (by linarith)
    href0 href (fun i hout => hfixed x (scale M (256*m) i) ⟨i,rfl⟩ (fun v hv =>
      hcover v (hex_region_subset_probe P (scale M (256*m) i) (M*scale M (256*m) i)
        (hinner.trans (mul_le_mul_of_nonneg_left
          (by exact_mod_cast base_le_scale (m := 256*m) (by omega : 1≤M) i) P.mesh_pos.le))
        hout hv)))
  have hsmall : 32*K*m≤latticeRadius x := by nlinarith only [hscale]
  have hreach := (RadialGapRadii.chosen_radii hK hm hd hsmall).2.2
  have hreach' : (latticeRadius x : ℝ)≤8*(K*RadialGapRadii.innerScale K (latticeRadius x) : ℕ) := by
    exact_mod_cast (show latticeRadius x≤8*(K*RadialGapRadii.innerScale K (latticeRadius x)) by
      nlinarith only [hreach])
  have houter : (latticeRadius x : ℝ)≤64*P.outerRadius := by
    dsimp only [P,probe]
    linarith only [hreach']
  have hρ : (0 : ℝ)<latticeRadius x := by
    exact_mod_cast (show 0<latticeRadius x by
      have hpos := Nat.mul_pos (Nat.mul_pos (by norm_num : 0<8192) (by omega : 0<K)) hm
      omega)
  have hP : 0<P.outerRadius := by linarith [P.inner_pos,P.radii]
  have hratio : 2*P.mesh*(256*m : ℕ)/P.outerRadius≤32768*((m : ℝ)/latticeRadius x) := by
    change 2*1*(256*m : ℕ)/(P.outerRadius)≤_
    push_cast
    apply (div_le_iff₀ hP).mpr
    apply (le_of_mul_le_mul_right (a := (latticeRadius x : ℝ)) ?_ hρ)
    field_simp
    nlinarith only [houter]
  apply hdecay.trans
  calc
    _ ≤ (2*(M : ℝ))^(2+h)*(32768*((m : ℝ)/latticeRadius x))^(2+h) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.mesh_pos.le) (Nat.cast_nonneg _)) hP.le)
        hratio (by linarith))
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤32768) (by positivity),
        ← mul_assoc,← Real.mul_rpow (by positivity) (by norm_num : (0 : ℝ)≤32768)]

#print axioms probe_decay_of_sampled_fixed_aspect

end ExceptionalTimes.SampledProbeDecay


