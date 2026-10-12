import ExceptionalTimes.ConcreteCanonicalDriver
import ExceptionalTimes.MatchingCollarComparison
import ExceptionalTimes.NolinAnnular

/-! Static origin one-arm literature inputs, with a literal finite fair-law
normalization. These are conventional consequences/reformulations of the
cited results, not verbatim statements with the source's original notation.

`PublishedOriginQuasiMultiplicativity` uses Nolin, arXiv:0711.4948v1,
section 4.5, Propositions 15 (extendability) and 16 (quasi-multiplicativity):
https://arxiv.org/html/0711.4948v1#S4.SS5 . Those statements include the
one-black-arm case j=1, whose microscopic radius is n0(1)=0. At p=1/2
the characteristic length is infinite. Nolin's oblique square annuli and
uncolored path endpoints are represented by `AnnularCrossing` below.
Passing to a black origin and exit from the closed box costs only fixed
endpoint and one-layer constants, absorbed using extendability. The
bounded-ratio comparison also follows by iterating extendability.

`PublishedOriginOneArmExponent` is the reciprocal power-bound consequence
of Lawler--Schramm--Werner, arXiv:math/0108211, Theorem 1.1:
https://arxiv.org/pdf/math/0108211 . The source uses a Euclidean circle;
fixed-shape norm comparison and one-layer changes preserve the exponent.
Positivity at the finitely many remaining microscopic scales, proved here,
allows one constant for all integer radii at least two.

Both predicates concern ordinary iid critical site percolation only. No
matching, dynamical, or paired-arm estimate is included as a source input.
-/

open scoped Classical BigOperators ENNReal

namespace ExceptionalTimes.OriginOneArmInputs

open EnvironmentVariance ProbeProduct PairSquareSewing FiniteHaar
open HoleFilling ActivePartitionLaw NolinCorridor

noncomputable def alpha (n : ℕ) : ℝ :=
  (ConcreteCanonicalDriver.finiteFairOneArm n).toReal

theorem alpha_eq_fair_probability (n : ℕ) :
    alpha n = probability (fairSites (latticeBox (n+1)))
      (fun η => OneArm (completeColors (latticeBox (n+1)) η) (0,0) n) := by
  exact ENNReal.toReal_ofReal (probability_nonneg _ _)

theorem alpha_pos (n : ℕ) : 0 < alpha n := by
  rw [alpha_eq_fair_probability]
  let D := latticeBox (n+1)
  let η : D → Bool := fun _ => true
  have hη : OneArm (completeColors D η) (0,0) n :=
    FairOneArm.oneArm_of_box_black n (fun v hv => by simp [completeColors,D,η,hv])
  have hw : 0 < (fairSites D).weight η := by
    simp only [fairSites,FiniteLaw.pi,ProbeProduct.fairBit]
    positivity
  have hsum := Finset.single_le_sum
    (s := Finset.univ) (f := fun ξ : D → Bool =>
      (fairSites D).weight ξ * indicator (OneArm (completeColors D ξ) (0,0) n))
    (fun ξ _ => mul_nonneg ((fairSites D).nonneg ξ) (indicator_nonneg _))
    (Finset.mem_univ η)
  have hi : indicator (OneArm (completeColors D η) (0,0) n) = 1 := by
    simp [indicator,hη]
  rw [hi,mul_one] at hsum
  exact hw.trans_le hsum

theorem alpha_nonneg (n : ℕ) : 0 ≤ alpha n := (alpha_pos n).le

theorem alpha_le_one (n : ℕ) : alpha n ≤ 1 := by
  rw [alpha_eq_fair_probability]
  exact probability_le_one _ _

theorem ofReal_alpha (n : ℕ) :
    ENNReal.ofReal (alpha n) = ConcreteCanonicalDriver.finiteFairOneArm n :=
  ENNReal.ofReal_toReal ENNReal.ofReal_ne_top

noncomputable def sourceAnnularProbability (r R : ℕ) : ℝ :=
  probability (fairSites (latticeBox (R+1)))
    (fun η => AnnularCrossing (completeColors (latticeBox (R+1)) η) r R)

/-- The critical one-arm consequences of Nolin's Propositions 15 and 16,
with endpoint and fixed-scale constants incorporated as described above. -/
def PublishedOriginQuasiMultiplicativity : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∃ A : ℝ, 1 ≤ A ∧
    (∀ s R : ℕ, 2 ≤ s → R ≤ M*s → alpha s ≤ A*alpha R) ∧
    (∀ s R : ℕ, 2 ≤ s → 2*s < R →
      alpha s * sourceAnnularProbability (2*s) R ≤ A*alpha R)

/-- The all-integer-radius reciprocal bound implied by the LSW one-arm
exponent, after the fixed-shape normalization described above. -/
def PublishedOriginOneArmExponent : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ B : ℝ, 0 < B ∧
    ∀ s : ℕ, 2 ≤ s → (alpha s)⁻¹ ≤ B*(s : ℝ)^(5/48+ζ)

/-- Every matching enumeration that covers the origin event has the same
ordinary one-arm marginal as the process-independent normalization. -/
theorem average_oneArm_eq_alpha {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (R : ℕ)
    (hcover : ∀ x ∈ latticeBox (R+1), ∃ b, slot b = x) :
    average (fun x => indicator (OneArm (pairDecode slot x) (0,0) R)) = alpha R := by
  rw [alpha_eq_fair_probability]
  exact FiniteSiteLaw.average_pairDecode_fairSites slot (latticeBox (R+1)) hcover _
    (fun _ _ he => oneArm_congr_of_eqOn_box (FairOneArm.origin_mem_latticeBox R) he)

/-- Actual wired means are bounded by the literal source annular event.
Only the actual annular support must be covered by the original slot. -/
theorem wiredMean_le_sourceProbability {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) {r R : ℕ} (hrR : r < R)
    (hcover : ∀ x ∈ annularSites r R, ∃ b, slot b = x) :
    average (fun x => indicator (WiredArm (pairDecode slot x) r R)) ≤
      sourceAnnularProbability r R := by
  rw [MatchingCollarComparison.average_wiredArm_of_local_cover slot
    (latticeBox (R+1)) hrR.le (fun _ hx => (Finset.mem_sdiff.mp hx).1) hcover]
  exact CanonicalRadialLaw.probability_mono _
    (fun _ h => wiredArm_implies_source_annular hrR h)

/-- The same quasi-multiplicative constant applies to the actual finite
matching decoder's ordinary wired mean; this is a proved event dictionary. -/
theorem origin_mul_wiredMean_le {A : ℝ}
    (hsource : ∀ s R : ℕ, 2 ≤ s → 2*s < R →
      alpha s * sourceAnnularProbability (2*s) R ≤ A*alpha R)
    {B : Type*} [Fintype B] (slot : B × Fin 2 ↪ Site)
    {s R : ℕ} (hs : 2 ≤ s) (hsR : 2*s < R)
    (hcover : ∀ x ∈ annularSites (2*s) R, ∃ b, slot b = x) :
    alpha s * average (fun x => indicator (WiredArm (pairDecode slot x) (2*s) R)) ≤
      A*alpha R :=
  (mul_le_mul_of_nonneg_left (wiredMean_le_sourceProbability slot hsR hcover)
    (alpha_nonneg s)).trans (hsource s R hs hsR)

#print axioms alpha_pos
#print axioms ofReal_alpha
#print axioms average_oneArm_eq_alpha
#print axioms wiredMean_le_sourceProbability
#print axioms origin_mul_wiredMean_le

end ExceptionalTimes.OriginOneArmInputs
