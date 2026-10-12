import ExceptionalTimes.LocalDimerCalibration
import ExceptionalTimes.CalibratedAnnulusMixing

/-! Literature boundary for ordinary INDEPENDENT site refresh, expressed
in a local pivotal-response clock. This is an explicitly assumed combined
published consequence, not a verbatim numbered theorem. Its deduction is
recorded in LocalAnnulusInputScope.txt. No swap estimate occurs here. -/

namespace ExceptionalTimes.LocalAnnulusInput

open LocalDimerCalibration IndependentAnnulusInput CalibratedAnnulusMixing

noncomputable def independentTime (T : ℝ) (n : ℕ) : ℝ :=
  T/(4*localClock .refresh n)

theorem independentTime_eq (T : ℝ) (n : ℕ) :
    independentTime T n=T*(mesh n)^2/(2*localS .refresh n) := by
  have h := local_clock_time .refresh n T
  unfold independentTime
  calc
    _=(T/(2*localClock .refresh n))/2 := by ring
    _=(T*(mesh n)^2/localS .refresh n)/2 := by rw [h]
    _=_ := by ring

/-- GHSS gamma=0 mixing and convergence, GPS static arm-event convergence,
ordinary central-site pivotal/four-arm comparison and the four-arm exponent.
The local refresh response is literal and contains no exclusion dynamics. -/
def PublishedIndependentLocalAnnulusMixing : Prop :=
  IndependentMixingAtTime independentTime

#print axioms independentTime_eq

end ExceptionalTimes.LocalAnnulusInput
