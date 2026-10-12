import ExceptionalTimes.RadialCanonicalAbsorption
import ExceptionalTimes.RadialAbsorptionScale
import ExceptionalTimes.OriginOneArmInputs
import ExceptionalTimes.CanonicalOriginBound
import ExceptionalTimes.CanonicalRadialEnergy

/-! The actual canonical matching energy follows from scale-dependent
paired probe decay. All choices of the integer hole ratio, the two radius
regimes, finite-law normalization, exponent losses and integration are
proved here. `NewScaleDependentProbeDecay` is explicitly NEW, not a
literature input: it retains exactly the paired-probe estimate and its
time-dependent mesoscopic scale. The other probability inputs are the
named static percolation theorems and the classical Efron--Stein inequality.
-/

open scoped Classical

namespace ExceptionalTimes.CanonicalEnergyFromProbeDecay

noncomputable section

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar HoleFilling
open ActivePartitionLaw ActiveMiddlePartition MesoscopicVariance
open RadialMixedAbsorption OriginOneArmInputs ConcreteCanonicalDriver

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

local instance {A O : Type*} [Fintype A] [Fintype O]
    (m : ℕ) (slot : ((A⊕O)×Fin 2) ↪ Site) : DecidableEq (Cells m slot) :=
  fun a b => Classical.propDecidable (a=b)

local instance {A O : Type*} [Fintype A] [Fintype O]
    (m : ℕ) (slot : ((A⊕O)×Fin 2) ↪ Site) (c : Cells m slot) :
    DecidableEq (Fiber m slot c) := fun a b => Classical.propDecidable (a=b)

local instance {B : Type*} (slot : B×Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ActiveLabels slot z S) := fun a b => Classical.propDecidable (a=b)

local instance {B : Type*} (slot : B×Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ExteriorLabels slot z S) := fun a b => Classical.propDecidable (a=b)

/-- The usual finite-product Efron--Stein theorem, uniformly over finite
alphabets. This is exactly the classical variance inequality already
isolated in `EnvironmentVariance.EfronStein`, not a percolation estimate. -/
def ClassicalFiniteEfronStein : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : I → Type) [∀ i,Fintype (A i)]
    (ρ : ∀ i,FiniteLaw (A i)), EfronStein ρ

/-- NEW and unproved. The actual homogeneous paired-probe probabilities
decay faster than the square of scale, at a mesoscopic scale bounded by
the stated time power. Only probes covered by the tested finite slot
occur in `NewPairedProbeDecay`. No origin probability or energy estimate
is assumed here. -/
def NewScaleDependentProbeDecay (z : Site) (B₀ : ℕ) : Prop :=
  ∀ η : ℝ,0<η → η<3/4 → ∀ K : ℕ,∀ hK : 2≤K,
    ∃ C : ℝ,0≤C ∧ ∃ h : ℝ,0<h ∧ ∃ D : ℝ,0≤D ∧
      ∃ m : ℝ→ℕ,∀ t∈Set.Ioo (0 : ℝ) 1,
        ∃ hm : 0<m t, B₀≤m t ∧ ∃ hd : latticeRadius z≤m t,
          (m t : ℝ)≤D*t^(-(1/(3/4-η))) ∧
          ∀ k : ℕ,∀ slot : Fin k×Fin 2 ↪ Site,
            (∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
            NewPairedProbeDecay slot K (m t) (latticeRadius z) hK hm hd
              (refreshProbability t) C h

theorem canonical_radial_power_of_new_probe_decay
    (boundaryInput : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PairSquareSewing.PublishedPolygonCrossingOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β)
    (hES : ClassicalFiniteEfronStein)
    (hquasi : PublishedOriginQuasiMultiplicativity)
    (hexponent : PublishedOriginOneArmExponent)
    (z : Site) (hz0 : z≠(0,0)) (hnew : NewScaleDependentProbeDecay z B₀) :
    CanonicalRadialEnergy.NewCanonicalRadialPower z := by
  obtain ⟨K,hK,δ,hδ,L,hL,c,hc,hannulus⟩ :=
    RadialCanonicalAbsorption.uniform_matching_bound_of_new_paired_decay
      boundaryInput hJordan hRSW hupper hβ
  intro ε hε
  obtain ⟨η,ζ,hη,hηsmall,hζ,hloss⟩ := exists_scale_exponent_losses hε
  obtain ⟨C,hC,h,hh,D,hD,m,hm⟩ := hnew η hη hηsmall K hK
  obtain ⟨N,hN,hN1,habsorb⟩ := RadialAbsorptionScale.exists_radial_ratio
    (8192*K+2) C δ h hC hδ hh
  let M := 64*L
  have hM : 2≤M := by dsimp only [M]; omega
  obtain ⟨A,hA,hsmall,hstatic⟩ := hquasi M hM
  obtain ⟨B,hB,harm⟩ := hexponent ζ hζ
  let Q : ℝ := 2/c^8
  have hQ : 0≤Q := by dsimp only [Q]; positivity
  let F : ℝ := A+Q*A^2
  have hF : 0≤F := by dsimp only [F]; positivity
  let U : ℝ := 5/48+ζ
  have hU : 0≤U := by dsimp only [U]; linarith
  refine ⟨F*B*((N : ℝ)*D)^U,by positivity,?_⟩
  intro R k slot hcover hpair t ht
  obtain ⟨hmt,hBm,hdt,hscale,hdecay⟩ := hm t ht
  let s := N*m t
  have hs : 2≤s := by dsimp only [s]; nlinarith
  have hds : latticeRadius z+1≤s := by dsimp only [s]; nlinarith
  have hz : z∈latticeBox (latticeRadius z) := mem_latticeBox_of_radius_le le_rfl
  have hcoverBox : ∀ v∈latticeBox (R+1),∃ b,slot b=v :=
    fun v hv => (hcover v).mp (FiniteMatchingClosure.subset_closure _ _ hv)
  have hp0 : ∀ _ : Fin k,0≤refreshProbability t :=
    fun _ => refreshProbability_nonneg ht.1.le
  have hp1 : ∀ _ : Fin k,refreshProbability t≤1 :=
    fun _ => refreshProbability_le_one t
  have hradial := CanonicalOriginBound.origin_relative_bound slot z hz hds hM hpair
    hcoverBox (fun _ => refreshProbability t) hp0 hp1 (by linarith : 0≤A) hQ
    (alpha_pos s) (hsmall s R hs) (fun hR =>
      origin_mul_wiredMean_le hstatic slot hs
        (lt_of_le_of_lt (Nat.mul_le_mul_right s hM) hR)
        (fun v hv => hcoverBox v (Finset.mem_sdiff.mp hv).1)) ?_
  · have hscaled : (s : ℝ)≤((N : ℝ)*D)*t^(-(1/(3/4-η))) := by
      dsimp only [s]
      push_cast
      exact (mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg N)).trans_eq (by ring)
    have hr : manyProbability (fun _ : Fin k => refreshProbability t)
        (fun x => OneArm (pairDecode slot x) (0,0) R) ≤
        F*(alpha R)^2*(alpha s)⁻¹ := by
      simpa only [F,Q,alpha,div_eq_mul_inv] using hradial
    exact radial_time_bound_of_scale ht.1 ht.2.le hF hB.le (by positivity)
      (Nat.cast_nonneg s) hU hscaled (harm s hs) hr hloss.le
  · intro hR
    have hwide : 32*L*(2*s)≤R := by
      have he : 32*L*(2*s)=M*s := by dsimp only [M]; ring
      omega
    apply hannulus slot z hz0 (m t) (latticeRadius z) (2*s) R hmt hBm hdt hz hpair
      (fun v hv => hcoverBox v (Finset.mem_sdiff.mp hv).1)
      (by dsimp only [s]; nlinarith) (by omega) hwide
      (fun _ => refreshProbability t) hp0 hp1
    · exact hES _ _ _
    · exact refreshProbability_nonneg ht.1.le
    · exact refreshProbability_le_one t
    · exact fun _ => le_rfl
    · exact hC
    · exact hh
    · exact hdecay k slot hpair
    · exact habsorb (m t) (2*s) hmt (by dsimp only [s]; omega)

/-- The full literal canonical energy bound, with its only new dynamical
premise reduced to the explicit scale-dependent paired probe decay. -/
theorem canonical_energy_of_new_probe_decay
    (boundaryInput : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PairSquareSewing.PublishedPolygonCrossingOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β)
    (hES : ClassicalFiniteEfronStein)
    (hquasi : PublishedOriginQuasiMultiplicativity)
    (hexponent : PublishedOriginOneArmExponent)
    (z : Site) (hz0 : z≠(0,0)) (hnew : NewScaleDependentProbeDecay z B₀) :
    FiniteMatchingExhaustion.CanonicalOneArmEnergyBound z (0,0) finiteFairOneArm :=
  CanonicalRadialEnergy.canonical_energy_of_radial_power z
    (canonical_radial_power_of_new_probe_decay boundaryInput hJordan hRSW hupper hβ
      hES hquasi hexponent z hz0 hnew)

/-- The precise energy premise of the concrete arbitrary-kernel driver
is discharged for every positive displacement by the same probe input. -/
theorem newCanonicalEnergy_of_new_probe_decay
    (boundaryInput : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PairSquareSewing.PublishedPolygonCrossingOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β)
    (hES : ClassicalFiniteEfronStein)
    (hquasi : PublishedOriginQuasiMultiplicativity)
    (hexponent : PublishedOriginOneArmExponent)
    (k : RateKernel)
    (hnew : ∀ z,0<k.rate z → NewScaleDependentProbeDecay z B₀) :
    ConcreteCanonicalDriver.NewCanonicalEnergy k := by
  intro z hz
  have hz0 : z≠(0,0) := by
    intro he
    have hd := k.diagonal
    rw [he] at hz
    change k.rate (0,0)=0 at hd
    linarith
  exact canonical_energy_of_new_probe_decay boundaryInput hJordan hRSW hupper hβ
    hES hquasi hexponent z hz0 (hnew z hz)

#print axioms canonical_radial_power_of_new_probe_decay
#print axioms canonical_energy_of_new_probe_decay
#print axioms newCanonicalEnergy_of_new_probe_decay

end

end ExceptionalTimes.CanonicalEnergyFromProbeDecay
