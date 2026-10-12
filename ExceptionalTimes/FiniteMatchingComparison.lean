import ExceptionalTimes.FiniteClockDomination
import ExceptionalTimes.FiniteMatchingClosure

open MeasureTheory Set
open scoped BigOperators ENNReal Classical Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace ExceptionalTimes.FiniteMatchingComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FiniteClockBridge FiniteClockComparison FiniteClockDomination FiniteMatchingClosure

theorem frame_event_iff (A V : Finset Site) (hAV : A ⊆ V) (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ)) (η : Configuration) :
    E η ↔ E (extendColor V (restrictColor V η)) := by
  apply hlocal
  intro x hx
  simp [extendColor, restrictColor, hAV hx]

theorem truncated_energy_frame {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate)
    (A V : Finset Site) (hAV : A ⊆ V) (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    (F : Finset (Sym2 Site)) (γ : ℝ) (ν : Measure ℝ) :
    P.truncatedCorrelationEnergy F E γ ν =
      P.truncatedCorrelationEnergy F (fun η => E (extendColor V (restrictColor V η))) γ ν := by
  unfold PoissonGraphicalRealization.truncatedCorrelationEnergy
  apply lintegral_congr
  intro t
  congr 1
  unfold PoissonGraphicalRealization.truncatedPairedCylinderProbability
  congr 1
  ext ω
  exact and_congr (frame_event_iff A V hAV E hlocal _) (frame_event_iff A V hAV E hlocal _)

/-- Vertices of the large finite exclusion cube outside the observation's
matching closure are inert in the comparison process. They are eliminated
by the proved finite support identity, not by assuming a product-law bridge. -/
theorem actual_energy_le_matching_law
    {Ξ Ψ I : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ψ] [Fintype I] [DecidableEq I]
    {μ : Measure Ξ} {ν : Measure Ψ} {rate slowRate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (Q : PoissonGraphicalRealization ν slowRate)
    (p : Site → Site) (hp : Function.Involutive p) (hfixed : ∀ x, p x ≠ x)
    (hslow : ∀ x, slowRate s(x, p x) = 1 / 2)
    (A V : Finset Site) (hV : closure p A ⊆ V) (edge : I → V × V)
    (hinj : Function.Injective (edgePair V edge)) (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (hsub : closureEdges p A ⊆ retainedEdges V edge)
    (hdom : ∀ x ∈ closure p A, 1 / 2 ≤ rate s(x, p x))
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ)) :
    ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ Site,
      (∀ x, x ∈ closure p A ↔ ∃ b, slot b = x) ∧
      (∀ b, slot (b, 1) = p (slot (b, 0))) ∧
      ∀ γ : ℝ, 0 ≤ γ → γ < 1 →
        P.truncatedCorrelationEnergy (retainedEdges V edge) E γ
          (volume.restrict (Ioc (0 : ℝ) 1)) ≤
          ENNReal.ofReal (Real.exp 1 + 1) *
            ∫⁻ t : ℝ in Ioc 0 1, frostmanKernel γ 0 t *
              ENNReal.ofReal (ManyDimerLaw.manyProbability (fun _ => DimerLaw.refreshProbability t)
                (fun η => E (decode slot η))) := by
  obtain ⟨k, slot, hcover, hpair, hcanonical⟩ := closure_cylinder_law Q p hp hfixed hslow A E hlocal
  have hslot (b : Fin k × Fin 2) : slot b ∈ V := hV ((hcover _).mpr ⟨b, rfl⟩)
  let slowEdge : Fin k → V × V := fun b =>
    (⟨slot (b, 0), hslot (b, 0)⟩, ⟨slot (b, 1), hslot (b, 1)⟩)
  have hpairEdge (b : Fin k) : edgePair V slowEdge b = s(slot (b, 0), p (slot (b, 0))) := by
    change s(slot (b, 0), slot (b, 1)) = _
    rw [hpair]
  have hrate (b : Fin k) : slowRate (edgePair V slowEdge b) = 1 / 2 := by
    rw [hpairEdge, hslow]
  have hsmall : retainedEdges V slowEdge = closureEdges p A :=
    enumeration_edges p hp A slot hcover hpair
  have hsinj : Function.Injective (edgePair V slowEdge) := MatchingDimerLaw.edge_injective slot
  have hslow0 : ∀ b, 0 ≤ slowRate (edgePair V slowEdge b) := by
    intro b
    rw [hrate]
    norm_num
  have horder := colorSwap_generator_subset_le V edge slowEdge hsinj
    (by rwa [hsmall]) rate slowRate hr (fun b => by
      rw [hrate, hpairEdge]
      exact hdom _ ((hcover _).mpr ⟨(b, 0), rfl⟩))
  refine ⟨k, slot, hcover, hpair, ?_⟩
  intro γ hγ0 hγ1
  have H := actual_energy_comparison V P Q edge slowEdge hinj hsinj hr hslow0 horder
    (fun η => E (extendColor V η)) hγ0 hγ1
  have hAV : A ⊆ V := (subset_closure p A).trans hV
  rw [← truncated_energy_frame P A V hAV E hlocal,
    ← truncated_energy_frame Q A V hAV E hlocal, hsmall] at H
  apply H.trans_eq
  congr 1
  unfold PoissonGraphicalRealization.truncatedCorrelationEnergy
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  rw [hcanonical t ht.1]

#print axioms actual_energy_le_matching_law

end ExceptionalTimes.FiniteMatchingComparison
