import ExceptionalTimes.FiniteClockEnergy

open MeasureTheory Set
open scoped BigOperators ENNReal Classical Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace ExceptionalTimes.FiniteClockComparison

open FiniteClockBridge FiniteClockEnergy FiniteGenerator FiniteFractional FiniteSpectralEnergy

variable {Ξ Ψ I J : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ψ]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The spectral energy comparison now applies to the literal graphical
models on their own supplied probability spaces. -/
theorem actual_energy_comparison {μ : Measure Ξ} {ν : Measure Ψ}
    {rate : Sym2 Site → ℝ} {slowRate : Sym2 Site → ℝ}
    (V : Finset Site) (P : PoissonGraphicalRealization μ rate)
    (Q : PoissonGraphicalRealization ν slowRate)
    (edge : I → V × V) (slowEdge : J → V × V)
    (hinj : Function.Injective (edgePair V edge))
    (hslowinj : Function.Injective (edgePair V slowEdge))
    (hr : ∀ i, 0 ≤ rate (edgePair V edge i))
    (hsr : ∀ j, 0 ≤ slowRate (edgePair V slowEdge j))
    (hAB : complexGenerator (fun j => colorSwap (slowEdge j).1 (slowEdge j).2)
        (fun j => slowRate (edgePair V slowEdge j)) ≤
      complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
        (fun i => rate (edgePair V edge i)))
    (E : (V → Bool) → Prop) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    P.truncatedCorrelationEnergy (retainedEdges V edge) (fun η => E (restrictColor V η)) γ
      (volume.restrict (Ioc (0 : ℝ) 1)) ≤
      ENNReal.ofReal (Real.exp 1 + 1) *
        Q.truncatedCorrelationEnergy (retainedEdges V slowEdge) (fun η => E (restrictColor V η)) γ
          (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have H := truncated_energy_le_comparator V P edge hinj hr
    (complexGenerator (fun j => colorSwap (slowEdge j).1 (slowEdge j).2)
      (fun j => slowRate (edgePair V slowEdge j)))
    (Matrix.nonneg_iff_posSemidef.mp (complexGenerator_nonneg _
      (fun _ => colorSwap_involutive _ _) _ hsr)) hAB E hγ0 hγ1
  apply H.trans_eq
  congr 1
  unfold PoissonGraphicalRealization.truncatedCorrelationEnergy
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  rw [truncated_cylinder_correlation V Q slowEdge hslowinj hsr t ht.1 E]

#print axioms actual_energy_comparison

end ExceptionalTimes.FiniteClockComparison
