import ExceptionalTimes.DimerSelectedDictionary
import ExceptionalTimes.ExpansionLimit
import ExceptionalTimes.IndependentAnnulusInput

/-! Exact clock calibrators: the degree-one coefficient of the actual
two-time crossing jump. The finite matching and its phase remain explicit. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.DimerJumpCalibration

open PairSquareSewing DimerLaw DimerExpansion ActivePartitionLaw
open CanonicalSpatialProduct BlockExpansion ExpansionLimit ProbeProduct EnvironmentVariance

noncomputable section

variable {B : Type*} [Fintype B]

def jumpTest (Q : PolygonQuad) (ω : TwoTimeConfiguration) : ℝ :=
  indicator (Q.test (ω false)≠Q.test (ω true))

def jumpCoefficient (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad)
    (u : History → ℝ) : ℝ :=
  coefficient (fun _ : B => base) (fun _ => u)
    (fun h => jumpTest Q (canonicalBackground slot (pairCoordinates.symm h))) 1

def canonicalJump (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad) : ℝ :=
  jumpCoefficient slot Q canonicalInsertion

def refreshJump (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad) : ℝ :=
  jumpCoefficient slot Q refreshInsertion

theorem coefficient_one {H : B → Type*} [∀ b,Fintype (H b)]
    (p u : ∀ b,H b → ℝ) (f : (∀ b,H b) → ℝ) :
    coefficient p u f 1=∑ b,selectedKernel p u {b} f := by
  have he : (Finset.univ : Finset (Finset B)).filter (fun S => S.card=1)=
      (Finset.univ : Finset B).powersetCard 1 := by
    ext S
    simp
  rw [coefficient,he,Finset.powersetCard_one,Finset.sum_map]
  rfl

theorem jumpCoefficient_eq_sum (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad)
    (u : History → ℝ) :
    jumpCoefficient slot Q u=∑ b,selectedKernel (fun _ : B => base) (fun _ => u) {b}
      (fun h => jumpTest Q (canonicalBackground slot (pairCoordinates.symm h))) :=
  coefficient_one _ _ _

theorem canonicalJump_eq_sum (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad) :
    canonicalJump slot Q=∑ b,selectedKernel (fun _ : B => base)
      (fun _ => canonicalInsertion) {b}
      (fun h => jumpTest Q (canonicalBackground slot (pairCoordinates.symm h))) :=
  jumpCoefficient_eq_sum _ _ _

theorem refreshJump_eq_sum (slot : B×Fin 2 ↪ Site) (Q : PolygonQuad) :
    refreshJump slot Q=∑ b,selectedKernel (fun _ : B => base)
      (fun _ => refreshInsertion) {b}
      (fun h => jumpTest Q (canonicalBackground slot (pairCoordinates.symm h))) :=
  jumpCoefficient_eq_sum _ _ _

#print axioms jumpCoefficient_eq_sum

end
end ExceptionalTimes.DimerJumpCalibration

