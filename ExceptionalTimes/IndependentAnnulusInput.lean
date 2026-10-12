import ExceptionalTimes.IndependentJointAssociation
import ExceptionalTimes.SourceReferenceGeometry
import ExceptionalTimes.CanonicalHexAnnuli

/-! An explicit literature boundary for INDEPENDENT site refresh.

The input below is a combined consequence, not a verbatim theorem:
Garban--Holden--Sepulveda--Sun 1905.06940v2 Theorems 1.3(i), 1.4(i),
Remark 1.5 at gamma=0; GPS 1008.1378v5 Lemma 2.9, the pivotal-count
normalization in its introduction, and the static alternating-four-arm
exponent 5/4. A fixed loss gives the displayed exponent 9/4 for two times.
No swap law occurs in the published input. Its transfer to swaps is NEW.

Time is actual site-refresh time T / E[number of Q0-pivotal sites].
The finite law, reference rectangle and pivotal count are literal below.
The statement is an explicit hypothesis; Lean does not certify citations.
-/

open scoped Classical BigOperators

namespace ExceptionalTimes.IndependentAnnulusInput

open EnvironmentVariance ProbeProduct PairSquareSewing CanonicalHexAnnuli
open IndependentJointAssociation DimerLaw

noncomputable section

def mesh (n : ℕ) : ℝ := ((2 : ℝ)^n)⁻¹

theorem mesh_pos (n : ℕ) : 0<mesh n := by unfold mesh; positivity

def reference (n : ℕ) : PolygonQuad := sourceReferenceAt (mesh n) (mesh_pos n) 0

def IsPivotal (Q : PolygonQuad) (v : Site) (ω : Configuration) : Prop :=
  Q.test (force {v} ω false)≠Q.test (force {v} ω true)

def pivotalMean (n : ℕ) : ℝ :=
  (fairSites (reference n).support).expect (fun ω =>
    ∑ v∈(reference n).support, indicator (IsPivotal (reference n) v (complete ω)))

theorem pivotalMean_nonneg (n : ℕ) : 0≤pivotalMean n := by
  apply FiniteLaw.expect_nonneg
  intro ω
  exact Finset.sum_nonneg (fun v _ => indicator_nonneg _)

def jointProbability (D : Finset Site) (t : ℝ) (E : Configuration→Prop) : ℝ :=
  ∑ ω : D→Bool×Bool, (∏ v,pairWeight (refreshProbability t) (ω v))*
    indicator (E (complete (fun v => (ω v).1)) ∧ E (complete (fun v => (ω v).2)))

theorem jointProbability_eq_law (D : Finset Site) (t : ℝ) (ht : 0≤t)
    (E : Configuration→Prop) :
    jointProbability D t E=
      probability (jointLaw (fun _ : D => refreshProbability t)
        (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t))
        (fun ω => E (complete (fun v => (ω v).1)) ∧ E (complete (fun v => (ω v).2))) := rfl

def annularProbability (M n : ℕ) (t : ℝ) : ℝ :=
  jointProbability (latticeBox (M*2^n)) t
    (HexFourArms 0 ((2^n : ℕ) : ℤ) ((M*2^n : ℕ) : ℤ))

/-- Published independent-dynamics consequence, including the fixed Q0
clock normalization. The large time may depend on M and the error, and
the small mesh threshold is chosen AFTER that time. -/
def PublishedIndependentAnnulusMixing : Prop :=
  ∃ C : ℝ,0≤C ∧ ∀ M : ℕ,2≤M → ∀ δ : ℝ,0<δ →
    ∃ T : ℝ,0<T ∧ ∃ N : ℕ,∀ n,N≤n →
      annularProbability M n (T/pivotalMean n)≤C*(M : ℝ)^(-(9/4 : ℝ))+δ

#print axioms pivotalMean_nonneg
#print axioms jointProbability_eq_law

end
end ExceptionalTimes.IndependentAnnulusInput
