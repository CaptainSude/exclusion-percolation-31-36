import ExceptionalTimes.RadialMixedAbsorption

/-! The actual full matching radial probability after mixed-law variance
absorption. All static collars, active labels, bulk positions, local
pivotal arms, and cell sums are constructed. The NEW homogeneous paired
four-arm decay remains displayed; it is not a published input here.
-/

open scoped Classical

namespace ExceptionalTimes.RadialCanonicalAbsorption

noncomputable section

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar
open MixedCanonicalLaw MixedAnnularCollar MesoscopicVariance
open ActivePartitionLaw ActiveMiddlePartition HoleFilling PairSquareSewing
open RadialMixedAbsorption

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

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

universe u

/-- Uniform constants precede the finite matching and all scales.
The only new probability premise is the explicitly named paired probe
decay. The remaining smallness condition is a literal scalar inequality. -/
theorem uniform_matching_bound_of_new_paired_decay
    (boundaryInput : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PublishedPolygonCrossingOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β) :
    ∃ K : ℕ, ∃ hK : 2≤K, ∃ δ : ℝ, 0<δ ∧
      ∃ L : ℕ, 2≤L ∧ ∃ c : ℝ, 0<c ∧
      ∀ {B : Type u} [Fintype B] (slot : B×Fin 2 ↪ Site) (z : Site),z≠(0,0) →
      ∀ m d r R : ℕ, ∀ hm : 0<m, B₀≤m → ∀ hd : d≤m, z∈latticeBox d →
        (∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
        (∀ v∈annularSites r R,∃ b,slot b=v) →
        8192*K*m≤r → 2≤r → 32*L*r≤R →
        ∀ (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1),
          let sl := splitSlot slot z (annularSites (2*r) (2*L*WideCollarRadii.outerStart L R))
          let pa := fun a : ActiveLabels slot z
            (annularSites (2*r) (2*L*WideCollarRadii.outerStart L R)) => p a.val
          let hp0a := fun a : ActiveLabels slot z
            (annularSites (2*r) (2*L*WideCollarRadii.outerStart L R)) => hp0 a.val
          let hp1a := fun a : ActiveLabels slot z
            (annularSites (2*r) (2*L*WideCollarRadii.outerStart L R)) => hp1 a.val
          EfronStein (fun cell => FiniteLaw.pi (fun a : Fiber m sl cell =>
            environmentLaw (pa a.val) (hp0a a.val) (hp1a a.val))) →
          ∀ a C h : ℝ,0≤a → a≤1 → (∀ i,a≤p i) → 0≤C → 0<h →
          NewPairedProbeDecay slot K m d hK hm hd a C h →
          98*(C/δ^6)*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h≤1/2 →
            manyProbability p (fun y => WiredArm (pairDecode slot y) r R) ≤
              (2/c^8)*(average (fun y => indicator (WiredArm (pairDecode slot y) r R)))^2 := by
  obtain ⟨K,hK,δ,hδ,hvar⟩ :=
    uniform_active_variance_of_new_paired_decay boundaryInput hJordan hRSW hupper hβ
  obtain ⟨L,hL,c,hc,hcollar⟩ := MatchingCollarComparison.uniform_matching_collar
    boundaryInput.graph_cut hRSW hupper hβ
  refine ⟨K,hK,δ,hδ,L,hL,c,hc,?_⟩
  intro B instB slot z hz0 m d r R hm hBm hd hz hp hcover hscale hr hwide p hp0 hp1
  dsimp only
  intro hES a C h ha0 ha1 hap hC hh hdecay hsmall
  have hmr : m≤r := by nlinarith
  have hR : 16*r≤R := by nlinarith
  have hdr : 2*d≤r := by nlinarith
  have htR := (WideCollarRadii.chosen_radii hL hr hwide).2.2.2.2.2.2.2.2.1
  have H := hvar slot z hz0 m d r R (2*r) (2*L*WideCollarRadii.outerStart L R)
    hm hBm hd hz hp hcover hscale (by omega) hR hdr le_rfl htR p hp0 hp1
    hES a C h ha0 ha1 hap hC hh hdecay
  dsimp only at H
  have hq := mixedProbability_nonneg
    (fun b : ActiveLabels slot z (annularSites (2*r) (2*L*WideCollarRadii.outerStart L R)) => p b.val)
    (fun b => hp0 b.val) (fun b => hp1 b.val)
    (fun y => WiredArm (splitDecode
      (splitSlot slot z (annularSites (2*r) (2*L*WideCollarRadii.outerStart L R))) y) r R)
  have hbound := absorb hq H hsmall
  have hc8 : 0≤c^8 := pow_nonneg hc.le 8
  apply (hcollar z hz0 r R hr (hBm.trans hmr) hwide slot hp hcover p hp0 hp1).trans
  apply (div_le_div_of_nonneg_right hbound hc8).trans_eq
  ring

#print axioms uniform_matching_bound_of_new_paired_decay

end

end ExceptionalTimes.RadialCanonicalAbsorption
