import Std

/-!
# Exact two-bit response identities for the periodic-dimer manuscript

This file uses only Lean's standard library.  All probability claims below are
encoded by exact counts in a sample space of 16 equally likely outcomes.

Start with two independent fair bits u,v.  The canonical kernel C chooses
identity or swap with equal probability.  We include an unused independent
fair bit so that its sample space also has size 16.  The refresh kernel M
chooses one of the two endpoints uniformly and replaces it by a fresh fair bit.

For EVERY increasing Boolean function of these two bits, not only a named
list of examples, we check the entire centered two-time output law.  Its four
integer coefficients, ordered 00,01,10,11 and divided by 16, are
  C: (-2,2,2,-2) for a dictator, and zero otherwise;
  M: (-2,2,2,-2) for a nonconstant function, and zero otherwise.
Equivalently, with w = (delta_01 + delta_10 - delta_00 - delta_11)/4,
the signed laws are (1/2)w in the stated cases.  No analytic percolation
statement, limit, or geometric sewing assertion is assumed or proved here.
-/

namespace DimerBinaryResponse

structure Table where
  ff : Bool
  ft : Bool
  tf : Bool
  tt : Bool
  deriving DecidableEq, Repr

def Table.eval (f : Table) : Bool → Bool → Bool
  | false, false => f.ff
  | false, true  => f.ft
  | true,  false => f.tf
  | true,  true  => f.tt

def Table.ofFunction (f : Bool → Bool → Bool) : Table :=
  ⟨f false false, f false true, f true false, f true true⟩

theorem Table.eval_ofFunction (f : Bool → Bool → Bool) (u v : Bool) :
    (Table.ofFunction f).eval u v = f u v := by
  cases u <;> cases v <;> rfl

-- Checking the four covering relations is equivalent to coordinatewise
-- monotonicity on the two-dimensional Boolean cube.
def Increasing (f : Table) : Prop :=
  (f.ff = true → f.ft = true) ∧
  (f.ff = true → f.tf = true) ∧
  (f.ft = true → f.tt = true) ∧
  (f.tf = true → f.tt = true)

instance (f : Table) : Decidable (Increasing f) :=
  inferInstanceAs (Decidable (
    (f.ff = true → f.ft = true) ∧
    (f.ff = true → f.tf = true) ∧
    (f.ft = true → f.tt = true) ∧
    (f.tf = true → f.tt = true)))

def IsDictator (f : Table) : Prop :=
  f = ⟨false, false, true, true⟩ ∨
  f = ⟨false, true, false, true⟩

instance (f : Table) : Decidable (IsDictator f) :=
  inferInstanceAs (Decidable (
    f = ⟨false, false, true, true⟩ ∨
    f = ⟨false, true, false, true⟩))

def IsConstant (f : Table) : Prop :=
  f = ⟨false, false, false, false⟩ ∨
  f = ⟨true, true, true, true⟩

instance (f : Table) : Decidable (IsConstant f) :=
  inferInstanceAs (Decidable (
    f = ⟨false, false, false, false⟩ ∨
    f = ⟨true, true, true, true⟩))

abbrev State := Bool × Bool
abbrev History := Bool × Bool

def bits : List Bool := [false, true]

-- First coin: choose whether to exchange the two colors; second coin: dummy.
def canonical (u v exchange _dummy : Bool) : State :=
  if exchange then (v, u) else (u, v)

-- First coin: choose the endpoint; second coin: new fair endpoint color.
def refresh (u v right newColor : Bool) : State :=
  if right then (u, newColor) else (newColor, v)

def frozen (u v _coin _dummy : Bool) : State := (u, v)

abbrev Kernel := Bool → Bool → Bool → Bool → State

def histories (f : Table) (K : Kernel) : List History :=
  bits.flatMap fun u =>
  bits.flatMap fun v =>
  bits.flatMap fun coin =>
  bits.map fun extra =>
    let after := K u v coin extra
    (f.eval u v, f.eval after.1 after.2)

theorem histories_length (f : Table) (K : Kernel) :
    (histories f K).length = 16 := by
  rfl

def historyCount (f : Table) (K : Kernel) (a b : Bool) : Nat :=
  ((histories f K).filter fun p => (p.1 == a) && (p.2 == b)).length

def jumpCount (f : Table) (K : Kernel) : Nat :=
  ((histories f K).filter fun p => p.1 != p.2).length

def centeredCount (f : Table) (K : Kernel) (a b : Bool) : Int :=
  Int.ofNat (historyCount f K a b) - Int.ofNat (historyCount f frozen a b)

structure Coefficients where
  ff : Int
  ft : Int
  tf : Int
  tt : Int
  deriving DecidableEq, Repr

def centeredLaw (f : Table) (K : Kernel) : Coefficients :=
  ⟨centeredCount f K false false, centeredCount f K false true,
   centeredCount f K true false, centeredCount f K true true⟩

def response : Coefficients := ⟨-2, 2, 2, -2⟩
def zeroLaw : Coefficients := ⟨0, 0, 0, 0⟩

-- Finite exhaustive checking is by the kernel-checked `decide` tactic.
-- Each theorem below universally quantifies over all 16 Boolean truth tables.

theorem canonical_centered_law (f : Table) :
    Increasing f → centeredLaw f canonical =
      if IsDictator f then response else zeroLaw := by
  cases f with
  | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem refresh_centered_law (f : Table) :
    Increasing f → centeredLaw f refresh =
      if IsConstant f then zeroLaw else response := by
  cases f with
  | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

-- Numerators at denominator 16: a jump probability is 4/16 = 1/4.
theorem canonical_jump_count (f : Table) :
    Increasing f → jumpCount f canonical =
      if IsDictator f then 4 else 0 := by
  cases f with
  | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem refresh_jump_count (f : Table) :
    Increasing f → jumpCount f refresh =
      if IsConstant f then 0 else 4 := by
  cases f with
  | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

-- Flow balance needs no monotonicity assumption.
theorem canonical_flow_balance (f : Table) :
    historyCount f canonical false true =
      historyCount f canonical true false := by
  cases f with
  | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem refresh_flow_balance (f : Table) :
    historyCount f refresh false true =
      historyCount f refresh true false := by
  cases f with
  | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> decide

-- Explicit quantification over an arbitrary Boolean function, rather than
-- requiring the caller to select one of six monotone named examples.
theorem arbitrary_function_response (f : Bool → Bool → Bool)
    (h : Increasing (Table.ofFunction f)) :
    (centeredLaw (Table.ofFunction f) canonical =
      if IsDictator (Table.ofFunction f) then response else zeroLaw) ∧
    (centeredLaw (Table.ofFunction f) refresh =
      if IsConstant (Table.ofFunction f) then zeroLaw else response) := by
  exact ⟨canonical_centered_law _ h, refresh_centered_law _ h⟩

-- A formulation using the usual coordinatewise order false <= true.
def BitLE (a b : Bool) : Prop := a = true → b = true

def CoordinatewiseIncreasing (f : Bool → Bool → Bool) : Prop :=
  ∀ u v u' v', BitLE u u' → BitLE v v' → BitLE (f u v) (f u' v')

theorem response_for_monotone_function (f : Bool → Bool → Bool)
    (h : CoordinatewiseIncreasing f) :
    (centeredLaw (Table.ofFunction f) canonical =
      if IsDictator (Table.ofFunction f) then response else zeroLaw) ∧
    (centeredLaw (Table.ofFunction f) refresh =
      if IsConstant (Table.ofFunction f) then zeroLaw else response) := by
  have false_le (b : Bool) : BitLE false b := by
    intro impossible
    cases impossible
  have le_refl (b : Bool) : BitLE b b := fun hb => hb
  apply arbitrary_function_response f
  exact ⟨h false false false true (false_le false) (false_le true),
    h false false true false (false_le true) (false_le false),
    h false true true true (false_le true) (le_refl true),
    h true false true true (le_refl true) (false_le true)⟩

#print axioms canonical_centered_law
#print axioms refresh_centered_law
#print axioms canonical_jump_count
#print axioms refresh_jump_count
#print axioms canonical_flow_balance
#print axioms refresh_flow_balance
#print axioms arbitrary_function_response
#print axioms response_for_monotone_function

end DimerBinaryResponse
