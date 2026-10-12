import ExceptionalTimes.FiniteSiteLaw
import ExceptionalTimes.AnnularCircuitProbability

open scoped Classical

namespace ExceptionalTimes.FairCircuitLaw

open HoleFilling AnnularCollars EnvironmentVariance ProbeProduct PairSquareSewing

noncomputable def flipColors (D : Finset Site) : (D→Bool) ≃ (D→Bool) where
  toFun ω v := !(ω v)
  invFun ω v := !(ω v)
  left_inv ω := by funext v; simp
  right_inv ω := by funext v; simp

theorem completeColors_monotone (D : Finset Site) : Monotone (completeColors D) := by
  intro a b hab v
  by_cases hv : v∈D
  · simpa only [completeColors,dite_eq_left hv] using hab ⟨v,hv⟩
  · simp only [completeColors,dite_eq_right hv,le_refl]

theorem probability_eq_average (D : Finset Site) (E : Configuration→Prop) :
    probability (fairSites D) (fun x => E (completeColors D x)) =
      FiniteHaar.average (fun x => indicator (E (completeColors D x))) :=
  FiniteSiteLaw.fairSites_expect_eq_average D _

theorem circuit_probability_complement
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (D : Finset Site) {r R : ℕ} (hrR : r≤R)
    (hD : annularSites r R ⊆ D) :
    probability (fairSites D) (fun x => BlackCircuit (completeColors D x) r (R+1)) =
      1-probability (fairSites D) (fun x => WiredArm (completeColors D x) r R) := by
  simp only [probability,FiniteSiteLaw.fairSites_expect_eq_average]
  apply blackCircuit_probability_complement boundaryInput (completeColors D) (flipColors D) hrR
  intro x v hv
  have hvD := hD hv
  simp only [completeColors,dite_eq_left hvD,flipColors,Equiv.coe_fn_mk]

#print axioms circuit_probability_complement

end ExceptionalTimes.FairCircuitLaw

