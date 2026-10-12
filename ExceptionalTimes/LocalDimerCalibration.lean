import ExceptionalTimes.SourcePolygonCalibration
import ExceptionalTimes.IndependentAnnulusInput

/-! The exact local reference clock matched by the common-square sewing
identity. It uses a single central pair and a literal static fair field;
it is distinct from the sum of pivotal responses over the reference quad. -/

open scoped Classical
namespace ExceptionalTimes.LocalDimerCalibration

open PairSquareSewing IndependentAnnulusInput

noncomputable def localS (rule : Rule) (n : ℕ) : ℝ :=
  averagedPairResponse (reference n).support rule (0 : Site) (1,0) (reference n).jump

noncomputable def localClock (rule : Rule) (n : ℕ) : ℝ :=
  localS rule n/(2*(mesh n)^2)

theorem localClock_pos (rule : Rule) (n : ℕ) (h : 0<localS rule n) :
    0<localClock rule n := div_pos h (by have := mesh_pos n; positivity)

theorem local_clock_time (rule : Rule) (n : ℕ) (T : ℝ) :
    T/(2*localClock rule n)=T*(mesh n)^2/localS rule n := by
  by_cases h : localS rule n=0
  · simp [localClock,h]
  · unfold localClock
    have he : mesh n≠0 := (mesh_pos n).ne'
    field_simp

#print axioms local_clock_time
end ExceptionalTimes.LocalDimerCalibration
