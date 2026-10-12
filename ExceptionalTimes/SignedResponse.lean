import BinaryResponse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
The finite signed-response calculation with an arbitrary external test.
Unlike a list of output counts, these identities can be inserted directly
inside a kernel integral. The exterior may be fixed arbitrarily; there is
no independence assumption on its relationship to the Boolean truth table.
This file does not assert that a percolation crossing factors through a
particular interior bit. That is the separate geometric sewing obligation.
-/

set_option autoImplicit false

open scoped BigOperators
open DimerBinaryResponse

namespace ExceptionalTimes.SignedResponse

/-- Evaluation against the universal signed two-time bit law. -/
noncomputable def bitResponse (test : History → ℝ) : ℝ :=
  (test (false, true) + test (true, false) -
    test (false, false) - test (true, true)) / 4

/-- The literal average of the updated response minus the frozen response,
over the four independent fair bits in the two-bit experiment. -/
noncomputable def pairResponse (f : Table) (K : Kernel) (test : History → ℝ) : ℝ :=
  (1 / 16) * ∑ u : Bool, ∑ v : Bool, ∑ coin : Bool, ∑ extra : Bool,
    (test (f.eval u v, f.eval (K u v coin extra).1 (K u v coin extra).2) -
      test (f.eval u v, f.eval u v))

noncomputable def canonicalAmplitude (f : Table) : ℝ :=
  if IsDictator f then 1 / 2 else 0

noncomputable def refreshAmplitude (f : Table) : ℝ :=
  if IsConstant f then 0 else 1 / 2

/-- The canonical pushforward identity tested against an arbitrary real
function of the two observed bits. -/
theorem canonical_response (f : Table) (hf : Increasing f) (test : History → ℝ) :
    pairResponse f canonical test = canonicalAmplitude f * bitResponse test := by
  rcases f with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Increasing, pairResponse, canonicalAmplitude, IsDictator,
      bitResponse, canonical, Table.eval] <;> ring

/-- The endpoint-refresh identity with exactly the same signed bit law. -/
theorem refresh_response (f : Table) (hf : Increasing f) (test : History → ℝ) :
    pairResponse f refresh test = refreshAmplitude f * bitResponse test := by
  rcases f with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Increasing, pairResponse, refreshAmplitude, IsConstant,
      bitResponse, refresh, Table.eval] <;> ring

/-- A nonzero insertion has an actual local-change witness, independently
of monotonicity or of the exterior test's values. -/
theorem exists_change_of_response_ne_zero (f : Table) (K : Kernel)
    (test : History → ℝ) (h : pairResponse f K test ≠ 0) :
    ∃ u v coin extra : Bool,
      f.eval u v ≠ f.eval (K u v coin extra).1 (K u v coin extra).2 := by
  by_contra hn
  push Not at hn
  apply h
  unfold pairResponse
  have heq : ∀ u v coin extra : Bool,
      test (f.eval u v, f.eval (K u v coin extra).1 (K u v coin extra).2) -
        test (f.eval u v, f.eval u v) = 0 := by
    intro u v coin extra
    rw [← hn u v coin extra, sub_self]
  simp only [heq, Finset.sum_const_zero, mul_zero]

/-- If the published local-change arm implication applies to every update,
then it applies whenever the signed response is nonzero. The implication
about arms is explicitly a premise, not smuggled into the finite algebra. -/
theorem response_supported_on_necessary_event (f : Table) (K : Kernel)
    (test : History → ℝ) (E : Prop)
    (hnecessary : ∀ u v coin extra : Bool,
      f.eval u v ≠ f.eval (K u v coin extra).1 (K u v coin extra).2 → E) :
    ¬ E → pairResponse f K test = 0 := by
  intro hE
  by_contra hn
  obtain ⟨u, v, coin, extra, hc⟩ := exists_change_of_response_ne_zero f K test hn
  exact hE (hnecessary u v coin extra hc)

/-- Constant exterior tests vanish, as required for a centered insertion. -/
@[simp] theorem bitResponse_const (r : ℝ) : bitResponse (fun _ => r) = 0 := by
  unfold bitResponse
  ring

theorem bitResponse_mul_const (test : History → ℝ) (r : ℝ) :
    bitResponse (fun h => test h * r) = bitResponse test * r := by
  unfold bitResponse
  ring

theorem bitResponse_const_mul (test : History → ℝ) (r : ℝ) :
    bitResponse (fun h => r * test h) = r * bitResponse test := by
  unfold bitResponse
  ring

/-- The two signed bit integrations commute, including for a test that
couples the two histories. -/
theorem bitResponse_comm (test : History → History → ℝ) :
    bitResponse (fun h => bitResponse (test h)) =
      bitResponse (fun k => bitResponse (fun h => test h k)) := by
  unfold bitResponse
  ring

/-- Abstract interchange after pushing each interior response to its bit.
The amplitudes travel with their interiors. The test can depend jointly on
both histories. The geometric successful seam must establish that its two
representations use this same test with the histories interchanged. -/
theorem signed_interchange
    (L R : (History → ℝ) → ℝ) (a b : ℝ)
    (hL : ∀ test, L test = a * bitResponse test)
    (hR : ∀ test, R test = b * bitResponse test)
    (test : History → History → ℝ) :
    L (fun h => R (test h)) = R (fun k => L (fun h => test h k)) := by
  simp only [hL, hR, bitResponse_const_mul]
  rw [bitResponse_comm]
  ring

end ExceptionalTimes.SignedResponse

#print axioms ExceptionalTimes.SignedResponse.canonical_response
#print axioms ExceptionalTimes.SignedResponse.refresh_response
#print axioms ExceptionalTimes.SignedResponse.signed_interchange
#print axioms ExceptionalTimes.SignedResponse.exists_change_of_response_ne_zero
