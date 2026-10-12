import Std

/-!
An explicit perfect matching with any prescribed nonzero displacement
on Z x Z. This is a different, coordinate-strip construction of the
matching used in the manuscript; no primitive-vector basis is needed.

The file concerns the matching alone, not operator domination or a
percolation estimate. All definitions are concrete integer operations.
-/

namespace ExceptionalTimes.PeriodicMatching

abbrev Point := Int × Int

def add (x y : Point) : Point := (x.1 + y.1, x.2 + y.2)
def sub (x y : Point) : Point := (x.1 - y.1, x.2 - y.2)

def coord (first : Bool) (x : Point) : Int :=
  if first then x.1 else x.2

theorem coord_add (first : Bool) (x y : Point) :
    coord first (add x y) = coord first x + coord first y := by
  cases first <;> rfl

theorem coord_sub (first : Bool) (x y : Point) :
    coord first (sub x y) = coord first x - coord first y := by
  cases first <;> rfl

theorem quotient_add_step (n d : Int) (hd : d ≠ 0) :
    (n + d) / d = n / d + 1 := by
  rw [Int.add_ediv_of_dvd_right (Int.dvd_refl d), Int.ediv_self hd]

theorem quotient_sub_step (n d : Int) (hd : d ≠ 0) :
    (n - d) / d = n / d - 1 := by
  rw [Int.sub_ediv_of_dvd n (Int.dvd_refl d), Int.ediv_self hd]

def height (first : Bool) (z x : Point) : Int :=
  coord first x / coord first z

def partnerOnAxis (first : Bool) (z x : Point) : Point :=
  if height first z x % 2 = 0 then add x z else sub x z

theorem height_add (first : Bool) (z x : Point)
    (hz : coord first z ≠ 0) :
    height first z (add x z) = height first z x + 1 := by
  unfold height
  rw [coord_add, quotient_add_step _ _ hz]

theorem height_sub (first : Bool) (z x : Point)
    (hz : coord first z ≠ 0) :
    height first z (sub x z) = height first z x - 1 := by
  unfold height
  rw [coord_sub, quotient_sub_step _ _ hz]

theorem partnerOnAxis_involutive (first : Bool) (z x : Point)
    (hz : coord first z ≠ 0) :
    partnerOnAxis first z (partnerOnAxis first z x) = x := by
  by_cases heven : height first z x % 2 = 0
  · have hodd : height first z (add x z) % 2 ≠ 0 := by
      rw [height_add first z x hz]
      omega
    simp only [partnerOnAxis, ite_eq_left heven, ite_eq_right hodd]
    apply Prod.ext <;> simp [add, sub]
  · have heven' : height first z (sub x z) % 2 = 0 := by
      rw [height_sub first z x hz]
      omega
    simp only [partnerOnAxis, ite_eq_right heven, ite_eq_left heven']
    apply Prod.ext <;> simp [add, sub]

theorem partnerOnAxis_ne_self (first : Bool) (z x : Point)
    (hz : coord first z ≠ 0) : partnerOnAxis first z x ≠ x := by
  intro h
  have hh := congrArg (height first z) h
  by_cases heven : height first z x % 2 = 0
  · simp only [partnerOnAxis, ite_eq_left heven] at hh
    rw [height_add first z x hz] at hh
    omega
  · simp only [partnerOnAxis, ite_eq_right heven] at hh
    rw [height_sub first z x hz] at hh
    omega

theorem partnerOnAxis_displacement (first : Bool) (z x : Point) :
    partnerOnAxis first z x = add x z ∨
    partnerOnAxis first z x = sub x z := by
  unfold partnerOnAxis
  split <;> simp

-- The chosen coordinate is nonzero whenever z is nonzero.
def chooseAxis (z : Point) : Bool := decide (z.1 ≠ 0)

theorem chosen_coord_ne_zero (z : Point) (hz : z ≠ (0, 0)) :
    coord (chooseAxis z) z ≠ 0 := by
  by_cases hfirst : z.1 = 0
  · have hsecond : z.2 ≠ 0 := by
      intro hsecond
      apply hz
      exact Prod.ext hfirst hsecond
    simpa [coord, chooseAxis, hfirst] using hsecond
  · simp [coord, chooseAxis, hfirst]

def partner (z x : Point) : Point := partnerOnAxis (chooseAxis z) z x

theorem partner_involutive (z : Point) (hz : z ≠ (0, 0)) (x : Point) :
    partner z (partner z x) = x :=
  partnerOnAxis_involutive _ _ _ (chosen_coord_ne_zero z hz)

theorem partner_ne_self (z : Point) (hz : z ≠ (0, 0)) (x : Point) :
    partner z x ≠ x :=
  partnerOnAxis_ne_self _ _ _ (chosen_coord_ne_zero z hz)

theorem partner_displacement (z x : Point) :
    partner z x = add x z ∨ partner z x = sub x z :=
  partnerOnAxis_displacement _ _ _

-- These three facts describe a concrete partition into two-point orbits.
theorem exists_displacement_matching (z : Point) (hz : z ≠ (0, 0)) :
    ∃ m : Point → Point,
      (∀ x, m (m x) = x) ∧ (∀ x, m x ≠ x) ∧
      (∀ x, m x = add x z ∨ m x = sub x z) :=
  ⟨partner z, partner_involutive z hz, partner_ne_self z hz,
    partner_displacement z⟩

def transverse (first : Bool) : Point :=
  if first then (0, 1) else (1, 0)

theorem coord_transverse (first : Bool) : coord first (transverse first) = 0 := by
  cases first <;> rfl

theorem partnerOnAxis_translate (first : Bool) (z w x : Point)
    (hparity : height first z (add x w) % 2 = height first z x % 2) :
    partnerOnAxis first z (add x w) = add (partnerOnAxis first z x) w := by
  simp only [partnerOnAxis, hparity]
  split <;> apply Prod.ext <;> simp only [add, sub] <;> omega

theorem partnerOnAxis_period_transverse (first : Bool) (z x : Point) :
    partnerOnAxis first z (add x (transverse first)) =
      add (partnerOnAxis first z x) (transverse first) := by
  apply partnerOnAxis_translate
  simp only [height, coord_add, coord_transverse, Int.add_zero]

theorem partnerOnAxis_period_twice (first : Bool) (z x : Point)
    (hz : coord first z ≠ 0) :
    partnerOnAxis first z (add x (add z z)) =
      add (partnerOnAxis first z x) (add z z) := by
  apply partnerOnAxis_translate
  have reassoc : add x (add z z) = add (add x z) z := by
    apply Prod.ext <;> simp only [add] <;> omega
  rw [reassoc, height_add first z (add x z) hz, height_add first z x hz]
  omega

def determinant (p q : Point) : Int := p.1 * q.2 - p.2 * q.1

theorem periods_independent (first : Bool) (z : Point)
    (hz : coord first z ≠ 0) :
    determinant (add z z) (transverse first) ≠ 0 := by
  cases first <;> simp only [coord, transverse, Bool.false_eq_true,
    ite_false, ite_true] at hz ⊢ <;>
    simp only [determinant, add, Int.mul_one, Int.mul_zero,
      Int.zero_sub, Int.sub_zero] <;> omega

/-- A fixed-point-free involution with only displacement z or -z and two
independent integer translation periods. Nonzero determinant expresses
independence of the periods; this does not invoke percolation. -/
theorem exists_periodic_displacement_matching (z : Point) (hz : z ≠ (0, 0)) :
    ∃ (m : Point → Point) (p q : Point),
      (∀ x, m (m x) = x) ∧ (∀ x, m x ≠ x) ∧
      (∀ x, m x = add x z ∨ m x = sub x z) ∧
      (∀ x, m (add x p) = add (m x) p) ∧
      (∀ x, m (add x q) = add (m x) q) ∧
      determinant p q ≠ 0 := by
  refine ⟨partner z, add z z, transverse (chooseAxis z),
    partner_involutive z hz, partner_ne_self z hz,
    partner_displacement z, ?_, ?_, ?_⟩
  · exact fun x => partnerOnAxis_period_twice _ _ _ (chosen_coord_ne_zero z hz)
  · exact partnerOnAxis_period_transverse _ _
  · exact periods_independent _ _ (chosen_coord_ne_zero z hz)

#print axioms partner_involutive
#print axioms partner_ne_self
#print axioms exists_displacement_matching
#print axioms exists_periodic_displacement_matching

end ExceptionalTimes.PeriodicMatching
