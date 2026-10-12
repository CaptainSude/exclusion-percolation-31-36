import ExceptionalTimes.SourcePolygonSewing

/-! Calibration identities for the literal closed-cell polygon test.
The square response is exactly half of the source's one-time Delta
response; both microscopic rules use the SAME actual jump observable. -/

open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing
open DimerBinaryResponse EnvironmentVariance

theorem PolygonQuad.crossing_mono (Q : PolygonQuad) {ω η : Configuration}
    (h : ∀ v, ω v=true → η v=true) (hc : Q.Crossing ω) : Q.Crossing η := by
  obtain ⟨a,ha,b,hb,hj⟩ := hc
  refine ⟨a,ha,b,hb,hj.mono ?_⟩
  rintro p ⟨⟨v,hv,hp⟩,hpQ⟩
  exact ⟨⟨v,h v hv,hp⟩,hpQ⟩

theorem PolygonQuad.test_mono (Q : PolygonQuad) {ω η : Configuration}
    (h : ∀ v, ω v=true → η v=true) : Q.test ω=true → Q.test η=true := by
  simp only [PolygonQuad.test,decide_eq_true_eq]
  exact Q.crossing_mono h

noncomputable def PolygonQuad.jump (Q : PolygonQuad) (η : TwoTimeConfiguration) : ℝ :=
  if Q.test (η false)≠Q.test (η true) then 1 else 0

theorem PolygonQuad.jump_bound (Q : PolygonQuad) (η : TwoTimeConfiguration) :
    |Q.jump η|≤1 := by
  unfold PolygonQuad.jump
  split <;> norm_num

namespace PolygonSewing

theorem square_crossing_mono (Q : PolygonQuad) (D : Finset Site) (ω : Configuration) :
    Q.test (force D ω false)=true → Q.test (force D ω true)=true := by
  apply Q.test_mono
  intro v hv
  by_cases hD : v ∈ D
  · simp [force,hD]
  · simpa [force,hD] using hv

theorem square_jump_half_pivotal (Q : PolygonQuad) (D : Finset Site) (ω : Configuration) :
    rawSquareResponse D (fun _ => ω) Q.jump =
      (boolValue (Q.test (force D ω true)) - boolValue (Q.test (force D ω false))) / 2 := by
  have hm := square_crossing_mono Q D ω
  cases h0 : Q.test (force D ω false) <;>
    cases h1 : Q.test (force D ω true) <;>
    simp_all [rawSquareResponse,SignedResponse.bitResponse,PolygonQuad.jump,
      squareHistory,boolValue]; norm_num

/-- Literal averaged source Delta-square response. -/
noncomputable def averagedSquareDelta (Λ : Finset Site) (D : Finset Site) (Q : PolygonQuad) : ℝ :=
  (ProbeProduct.fairSites ↥Λ).expect (fun ω =>
    boolValue (Q.test (force D (complete ω) true)) -
      boolValue (Q.test (force D (complete ω) false)))

theorem averaged_square_jump_half_pivotal (Λ : Finset Site) (D : Finset Site) (Q : PolygonQuad) :
    averagedSquareResponse Λ D Q.jump=averagedSquareDelta Λ D Q/2 := by
  unfold averagedSquareResponse averagedSquareDelta
  simp_rw [square_jump_half_pivotal,div_eq_mul_inv]
  exact FiniteLaw.expect_mul_const _ _ _

theorem square_jump_lower_of_delta (Λ : Finset Site) (D : Finset Site) (Q : PolygonQuad)
    (c a : ℝ) (h : c*a≤averagedSquareDelta Λ D Q) :
    (c/2)*a≤averagedSquareResponse Λ D Q.jump := by
  rw [averaged_square_jump_half_pivotal]
  linarith

noncomputable def pairJoinTable (Q : PolygonQuad) (ω : Configuration) (x z : Site) : Table :=
  Table.ofFunction (fun u v => Q.test (putPair ω x z u v))

@[simp] theorem pairJoinTable_eval (Q : PolygonQuad) (ω : Configuration)
    (x z : Site) (u v : Bool) :
    (pairJoinTable Q ω x z).eval u v = Q.test (putPair ω x z u v) :=
  Table.eval_ofFunction _ u v

/-- This is graph-path monotonicity, not an additional necklace hypothesis. -/
theorem pairJoinTable_increasing (Q : PolygonQuad) (ω : Configuration) (x z : Site) :
    Increasing (pairJoinTable Q ω x z) := by
  change (Q.test (putPair ω x z false false) = true →
      Q.test (putPair ω x z false true) = true) ∧
    (Q.test (putPair ω x z false false) = true →
      Q.test (putPair ω x z true false) = true) ∧
    (Q.test (putPair ω x z false true) = true →
      Q.test (putPair ω x z true true) = true) ∧
    (Q.test (putPair ω x z true false) = true →
      Q.test (putPair ω x z true true) = true)
  exact ⟨Q.test_mono (putPair_mono ω x z id (by simp)),
    Q.test_mono (putPair_mono ω x z (by simp) id),
    Q.test_mono (putPair_mono ω x z (by simp) id),
    Q.test_mono (putPair_mono ω x z id (by simp))⟩

/-- The pair jump amplitude is derived from its actual two-site
monotone truth table for either literal update rule. -/
theorem pair_jump_half_amplitude (rule : Rule) (Q : PolygonQuad)
    (ω : Configuration) (x z : Site) :
    rawPairResponse rule.kernel (fun _ => ω) x z Q.jump =
      rule.amplitude (pairJoinTable Q ω x z) / 2 := by
  have h := rule.response (pairJoinTable Q ω x z) (pairJoinTable_increasing Q ω x z)
    (fun h : History => if h.1≠h.2 then (1:ℝ) else 0)
  norm_num [SignedResponse.pairResponse,rawPairResponse,PolygonQuad.jump,pairHistory,
    SignedResponse.bitResponse,pairJoinTable_eval,div_eq_mul_inv] at h ⊢
  exact h

#print axioms square_jump_half_pivotal
#print axioms averaged_square_jump_half_pivotal
#print axioms square_jump_lower_of_delta
#print axioms pair_jump_half_amplitude
end PolygonSewing
end ExceptionalTimes.PairSquareSewing
