import Std

/-!
# First-success selection of involutions

A finite ordered list of trials carries Boolean success tests and maps T_i.
Each T_i is an involution.  If trial i succeeds, applying T_i preserves every
trial's success test.  We prove that applying the first successful map (or
doing nothing when no trial succeeds) is itself an involution and a bijection.

Selector invariance is proved from test invariance; it is NOT an assumption
that the adaptive map is a bijection.  There is no measure or probability
claim in this file.  In particular, a bijection on a general probability
space need not preserve its measure.
-/

namespace AdaptiveExchange

universe u v w
variable {State : Type u} {Trial : Type v}

def select (success : Trial → State → Bool) (trials : List Trial)
    (x : State) : Option Trial :=
  trials.find? (fun i => success i x)

def applyFirst (success : Trial → State → Bool)
    (transform : Trial → State → State) (trials : List Trial)
    (x : State) : State :=
  match select success trials x with
  | none => x
  | some i => transform i x

theorem selected_success (success : Trial → State → Bool)
    (trials : List Trial) (x : State) (i : Trial) :
    select success trials x = some i → success i x = true := by
  induction trials with
  | nil =>
    simp [select, List.find?]
  | cons j remaining ih =>
    intro hselected
    cases hj : success j x with
    | false =>
      apply ih
      simpa [select, List.find?, hj] using hselected
    | true =>
      have hji : j = i := by
        simpa [select, List.find?, hj] using hselected
      simpa [← hji] using hj

-- This derives preservation of the entire selector from preservation of
-- individual Boolean test values under a successful trial's map.
theorem selector_invariant (success : Trial → State → Bool)
    (transform : Trial → State → State) (trials : List Trial)
    (preservesTests : ∀ i x, success i x = true →
      ∀ j, success j (transform i x) = success j x)
    (x : State) (i : Trial) (hi : success i x = true) :
    select success trials (transform i x) = select success trials x := by
  have predicates_equal :
      (fun j => success j (transform i x)) = (fun j => success j x) := by
    funext j
    exact preservesTests i x hi j
  unfold select
  rw [predicates_equal]

theorem applyFirst_involutive (success : Trial → State → Bool)
    (transform : Trial → State → State) (trials : List Trial)
    (eachInvolutive : ∀ i x, transform i (transform i x) = x)
    (preservesTests : ∀ i x, success i x = true →
      ∀ j, success j (transform i x) = success j x)
    (x : State) :
    applyFirst success transform trials
      (applyFirst success transform trials x) = x := by
  cases hs : select success trials x with
  | none =>
    simp [applyFirst, hs]
  | some i =>
    have hi : success i x = true := selected_success success trials x i hs
    have hs' : select success trials (transform i x) = some i :=
      (selector_invariant success transform trials preservesTests x i hi).trans hs
    simpa only [applyFirst, hs, hs'] using eachInvolutive i x

-- Written out so this file does not depend on a library definition of
-- bijectivity.  The two conjuncts are injectivity and surjectivity.
theorem applyFirst_bijective (success : Trial → State → Bool)
    (transform : Trial → State → State) (trials : List Trial)
    (eachInvolutive : ∀ i x, transform i (transform i x) = x)
    (preservesTests : ∀ i x, success i x = true →
      ∀ j, success j (transform i x) = success j x) :
    (∀ x y, applyFirst success transform trials x =
      applyFirst success transform trials y → x = y) ∧
    (∀ y, ∃ x, applyFirst success transform trials x = y) := by
  have twice := applyFirst_involutive success transform trials
    eachInvolutive preservesTests
  constructor
  · intro x y h
    calc
      x = applyFirst success transform trials
          (applyFirst success transform trials x) := (twice x).symm
      _ = applyFirst success transform trials
          (applyFirst success transform trials y) :=
        congrArg (applyFirst success transform trials) h
      _ = y := twice y
  · intro y
    exact ⟨applyFirst success transform trials y, twice y⟩

-- Pointwise weight preservation needs only the success-set hypothesis.
-- Together with the preceding bijection theorem this supplies the algebra
-- used for a finite weighted distribution.  We do not assert an abstract
-- measure-preservation result on arbitrary measurable spaces.
theorem applyFirst_preserves_weight {Weight : Type w}
    (success : Trial → State → Bool)
    (transform : Trial → State → State) (trials : List Trial)
    (weight : State → Weight)
    (preservesWeight : ∀ i x, success i x = true →
      weight (transform i x) = weight x)
    (x : State) :
    weight (applyFirst success transform trials x) = weight x := by
  cases hs : select success trials x with
  | none =>
    simp [applyFirst, hs]
  | some i =>
    have hi : success i x = true := selected_success success trials x i hs
    simpa only [applyFirst, hs] using preservesWeight i x hi

#print axioms selected_success
#print axioms selector_invariant
#print axioms applyFirst_involutive
#print axioms applyFirst_bijective
#print axioms applyFirst_preserves_weight

end AdaptiveExchange
