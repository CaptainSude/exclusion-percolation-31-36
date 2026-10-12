import ExceptionalTimes.RadialFourArmProbe
import ExceptionalTimes.CanonicalParameterOrder
import ExceptionalTimes.ActivePartitionLaw

/-! The local term in radial cell pivotality is compared to the actual
homogeneous canonical four-arm probability. The deterministic necessity
of these arms remains an explicit, unproved premise; their probability
decay is not asserted in this module. -/

namespace ExceptionalTimes.CanonicalRadialLocal

open DimerLaw ManyDimerLaw MixedCanonicalLaw MixedAnnularCollar ActivePartitionLaw
open PairSquareSewing MesoscopicCells HoleFilling RadialFourArmProbe

variable {A O : Type*} [Fintype A] [Fintype O]

theorem mixed_le_homogeneous (slot : ((A⊕O)×Fin 2) ↪ Site)
    (p : A→ℝ) (hp1 : ∀ a,p a≤1) (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1)
    (hup : ∀ a,u≤p a) (E : Configuration→Prop) :
    mixedProbability p (fun x => E (splitDecode slot x))≤
      manyProbability (fun _ : A⊕O => u) (fun x => E (pairDecode slot x)) := by
  have h := CanonicalParameterOrder.mixedProbability_le_manyProbability
    (fun _ : A => u) p (fun _ : O => u) (fun _ => hu0) hup hp1
    (fun _ => hu0) (fun _ => hu1) (fun x => E (splitDecode slot x))
  have hparam : Sum.elim (fun _ : A => u) (fun _ : O => u)=(fun _ => u) := by
    funext b
    cases b <;> rfl
  have hdecode (x : A⊕O→Color) :
      splitDecode slot (fun a => x (.inl a),fun o => x (.inr o))=pairDecode slot x := by
    rw [splitDecode_eq_pairDecode]
    congr 1
    funext b
    cases b <;> rfl
  simpa only [hparam,hdecode] using h

universe u v

/-- Uniform constants are chosen before the finite label types. All
locality, displacement buffers and spatial independence have been
discharged. Only the named local four-arm necessity is a premise. -/
theorem uniform_pivotal_canonical_fourArms
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0<β) :
    ∃ K : ℕ, ∃ hK : 2≤K, ∃ δ : ℝ, 0<δ ∧
      ∀ {A : Type u} {O : Type v} [Fintype A] [Fintype O]
        (slot : ((A⊕O)×Fin 2) ↪ Site) (z : Site) (m d r R : ℕ)
        (hm : 0<m), B₀≤m → ∀ hd : d≤m, z∈latticeBox d →
        (∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
        (∀ s∈annularSites r R, ∃ ie, slot ie=s) →
        ∀ cell∈occupied m (MesoscopicVariance.activeSlot slot),
          let x := anchor m (MesoscopicVariance.activeSlot slot) cell
          let ρ := anchorRadius m (MesoscopicVariance.activeSlot slot) cell
          ∀ hscale : 8192*K*m≤ρ, r≤ρ → ρ≤R →
          (∀ ω, CellInterpolation.CellPivotal (wiredArmTest r R)
            (dimerCell m (MesoscopicVariance.activeSlot slot) cell) ω →
              FourArms (probe x K m d hK hm hd hscale) ω) →
          ∀ (p : A→ℝ), (∀ i,0≤p i) → (∀ i,p i≤1) →
          ∀ a : ℝ, 0≤a → a≤1 → (∀ i,a≤p i) →
            mixedProbability p (fun y => CellInterpolation.CellPivotal (wiredArmTest r R)
              (dimerCell m (MesoscopicVariance.activeSlot slot) cell) (splitDecode slot y)) ≤
              manyProbability (fun _ : A⊕O => a)
                (fun y => FourArms (probe x K m d hK hm hd hscale) (pairDecode slot y)) *
                mixedProbability p (fun y => WiredArm (splitDecode slot y) r R)/δ^6 := by
  obtain ⟨K,hK,δ,hδ,hreduce⟩ :=
    RadialSeparatedLaw.uniform_pivotal_local_reduction boundaryInput hRSW hupper hβ
  refine ⟨K,hK,δ,hδ,?_⟩
  intro A O instA instO slot z m d r R hm hBm hd hz hp hcover cell hc
  dsimp only
  intro hscale hr hR hnecessary p hp0 hp1 a ha0 ha1 hap
  let x := anchor m (MesoscopicVariance.activeSlot slot) cell
  let P := probe x K m d hK hm hd hscale
  have hsmall : 32*K*m≤anchorRadius m (MesoscopicVariance.activeSlot slot) cell := by
    nlinarith
  have h := hreduce slot z m d r R hm hBm hd hz hp hcover cell hc hsmall hr hR
    (FourArms P) (probe_locality x K m d hK hm hd hscale) hnecessary p hp0 hp1
  apply h.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hδ.le 6)
  exact mul_le_mul_of_nonneg_right
    (mixed_le_homogeneous slot p hp1 a ha0 ha1 hap (FourArms P))
    (mixedProbability_nonneg p hp0 hp1 _)

#print axioms mixed_le_homogeneous
#print axioms uniform_pivotal_canonical_fourArms

end ExceptionalTimes.CanonicalRadialLocal
