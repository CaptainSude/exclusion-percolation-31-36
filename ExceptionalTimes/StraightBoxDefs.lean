import ExceptionalTimes.PolygonLocalChange

/-! A straight axial rectangle whose boundary passes through the terminal-row
centers. Its four sides are macroscopic segments, not polyhex sawteeth. -/

open Set

namespace ExceptionalTimes.PairSquareSewing

def axialRectangle (n : ℕ) : Set (ℝ × ℝ) :=
  (Icc (-(n:ℝ)) n).prod (Icc (-(n:ℝ)) n)

def straightLeft (n : ℕ) : Set (ℝ × ℝ) :=
  {p | p.1 = -(n:ℝ) ∧ p.2 ∈ Icc (-(n:ℝ)) n}

def straightRight (n : ℕ) : Set (ℝ × ℝ) :=
  {p | p.1 = (n:ℝ) ∧ p.2 ∈ Icc (-(n:ℝ)) n}

def straightTop (n : ℕ) : Set (ℝ × ℝ) :=
  {p | p.2 = (n:ℝ) ∧ p.1 ∈ Icc (-(n:ℝ)) n}

def straightBottom (n : ℕ) : Set (ℝ × ℝ) :=
  {p | p.2 = -(n:ℝ) ∧ p.1 ∈ Icc (-(n:ℝ)) n}

def StraightBoxCrossing (n : ℕ) (ω : Configuration) : Prop :=
  ∃ a ∈ straightLeft n, ∃ b ∈ straightRight n,
    JoinedIn (globalBlackCells ω ∩ axialRectangle n) a b

end ExceptionalTimes.PairSquareSewing
