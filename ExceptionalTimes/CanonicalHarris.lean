import ExceptionalTimes.FiniteHaar
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Independent finite block refreshes and duplicated Harris association. -/

open scoped BigOperators Classical
open ExceptionalTimes.FiniteHaar

namespace ExceptionalTimes.CanonicalHarris

variable {B G X : Type*} [Fintype B] [Group G] [Fintype G]
  [Fintype X] [MulAction G X]

/-- Set the group element to the identity at every unrefreshed block. -/
def mask (s : B → Bool) (g : B → G) : B → G := fun b => if s b then g b else 1

/-- Apply the chosen permutation independently in each refreshed block. -/
def refresh (s : B → Bool) (g : B → G) (ω : B → X) : B → X :=
  fun b => mask s g b • ω b

@[instance_reducible] def maskedAction (s : B → Bool) : MulAction (B → G) (B → X) where
  smul := refresh s
  one_smul ω := by
    change refresh s 1 ω = ω
    funext b
    cases hs : s b <;> simp [refresh, mask, hs]
  mul_smul g k ω := by
    change refresh s (g * k) ω = refresh s g (refresh s k ω)
    funext b
    cases hs : s b <;> simp [refresh, mask, hs, mul_smul]

noncomputable def project (s : B → Bool) (f : (B → X) → ℝ) : (B → X) → ℝ :=
  letI := maskedAction (G := G) (X := X) s
  reynolds (G := B → G) f

/-- The conditional two-time coefficient, with the refreshed blocks fixed. -/
noncomputable def conditional (f : (B → X) → ℝ) (s : B → Bool) : ℝ :=
  letI := maskedAction (G := G) (X := X) s
  average (fun g : B → G => coefficient f g)

omit [Fintype B] [Fintype G] in
theorem mask_mask {s t : B → Bool} (hst : s ≤ t) (g : B → G) :
    mask t (mask s g) = mask s g := by
  funext b
  have hb := hst b
  cases hs : s b <;> cases ht : t b <;> simp [mask, hs, ht] at hb ⊢
  exact False.elim (Bool.false_lt_true.not_ge hb)

omit [Fintype X] in
theorem project_invariant {s t : B → Bool} (hst : s ≤ t)
    (f : (B → X) → ℝ) (g : B → G) (ω : B → X) :
    project (G := G) t f (refresh s g ω) = project (G := G) t f ω := by
  let := maskedAction (G := G) (X := X) t
  have he : refresh s g ω = refresh t (mask s g) ω := by
    unfold refresh
    rw [mask_mask hst]
  rw [he]
  exact reynolds_invariant f (mask s g) ω

theorem conditional_eq (f : (B → X) → ℝ) (s : B → Bool) :
    conditional (G := G) f s = (Fintype.card (B → X) : ℝ)⁻¹ *
      dot f (project (G := G) s f) := by
  let := maskedAction (G := G) (X := X) s
  unfold conditional project
  simp only [coefficient_eq, average_const_mul, dot_reynolds]

theorem dot_project_square (f : (B → X) → ℝ) (s : B → Bool) :
    dot f (project (G := G) s f) =
      dot (project (G := G) s f) (project (G := G) s f) := by
  let := maskedAction (G := G) (X := X) s
  exact dot_reynolds_square f

/-- Adding refreshed blocks decreases the conditional coefficient.
This is derived from the actual finite group averages. -/
theorem conditional_antitone (f : (B → X) → ℝ) : Antitone (conditional (G := G) f) := by
  intro s t hst
  have hdot : dot (project (G := G) s f) (project (G := G) t f) =
      dot (project (G := G) t f) (project (G := G) t f) := by
    let := maskedAction (G := G) (X := X) s
    calc
      _ = dot f (project (G := G) t f) :=
        dot_invariant f _ (project_invariant hst f)
      _ = _ := dot_project_square f t
  simp only [conditional_eq, dot_project_square]
  exact mul_le_mul_of_nonneg_left (dot_square_lower _ _ hdot) (by positivity)

theorem conditional_nonneg (f : (B → X) → ℝ) (s : B → Bool) :
    0 ≤ conditional (G := G) f s := by
  rw [conditional_eq, dot_project_square]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun x _ => mul_self_nonneg _)

theorem conditional_square_lower [Nonempty X] (f : (B → X) → ℝ) (s : B → Bool) :
    (average f)^2 ≤ conditional (G := G) f s := by
  let := maskedAction (G := G) (X := X) s
  exact haar_mean_square_lower f

theorem conditional_association [DistribLattice X] [Nonempty X]
    (hact : ∀ g : G, Monotone (fun x : X => g • x))
    (f h : (B → X) → ℝ) (hf0 : ∀ ω, 0 ≤ f ω) (hh0 : ∀ ω, 0 ≤ h ω)
    (hf : Monotone f) (hh : Monotone h) (s : B → Bool) :
    conditional (G := G) f s * conditional (G := G) h s ≤
      conditional (G := G) (fun ω => f ω * h ω) s := by
  let := maskedAction (G := G) (X := X) s
  apply haar_positive_association _ f h hf0 hh0 hf hh
  intro g ω η hωη b
  exact hact (mask s g b) (hωη b)

section Flags

/-- Product Bernoulli mass of an exact refresh-flag configuration. -/
noncomputable def flagWeight (p : B → ℝ) (s : B → Bool) : ℝ :=
  ∏ b, if s b then p b else 1 - p b

theorem flagWeight_nonneg (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (s : B → Bool) : 0 ≤ flagWeight p s := by
  apply Finset.prod_nonneg
  intro b _
  cases s b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr (hp1 b)
  · exact hp0 b

/-- The independent Bernoulli flag weights form a probability law. -/
theorem flagWeight_sum (p : B → ℝ) : ∑ s, flagWeight p s = 1 := by
  unfold flagWeight
  rw [← Fintype.prod_sum (fun b (v : Bool) => if v then p b else 1 - p b)]
  simp

/-- Product weights satisfy the FKG lattice condition with equality. -/
theorem flagWeight_modular (p : B → ℝ) (s t : B → Bool) :
    flagWeight p s * flagWeight p t = flagWeight p (s ⊓ t) * flagWeight p (s ⊔ t) := by
  simp only [flagWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  cases hs : s b <;> cases ht : t b <;> simp [hs, ht, Pi.inf_apply, Pi.sup_apply, mul_comm]

noncomputable def flagAverage (p : B → ℝ) (f : (B → Bool) → ℝ) : ℝ :=
  ∑ s, flagWeight p s * f s

theorem flagAverage_const (p : B → ℝ) (c : ℝ) : flagAverage p (fun _ => c) = c := by
  rw [flagAverage, ← Finset.sum_mul, flagWeight_sum, one_mul]

theorem flagAverage_mono (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    {f h : (B → Bool) → ℝ} (hle : ∀ s, f s ≤ h s) : flagAverage p f ≤ flagAverage p h := by
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hle s)
    (flagWeight_nonneg p hp0 hp1 s))

/-- Harris inequality for decreasing functions of independent refresh flags. -/
theorem flag_harris_antitone (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (f h : (B → Bool) → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hh0 : ∀ s, 0 ≤ h s)
    (hf : Antitone f) (hh : Antitone h) :
    flagAverage p f * flagAverage p h ≤ flagAverage p (fun s => f s * h s) := by
  have hfk := fkg (α := (B → Bool)ᵒᵈ) f h (flagWeight p)
    (flagWeight_nonneg p hp0 hp1) hf0 hh0
    (by intro a b hab; exact hf hab) (by intro a b hab; exact hh hab)
    (fun a b => le_of_eq ((flagWeight_modular p a b).trans (mul_comm _ _)))
  have hsum : (∑ a : (B → Bool)ᵒᵈ, flagWeight p a) = 1 := flagWeight_sum p
  rw [hsum, one_mul] at hfk
  exact hfk

end Flags

/-- Two-time coefficient for independently refreshed disjoint finite blocks. -/
noncomputable def canonical (p : B → ℝ) (f : (B → X) → ℝ) : ℝ :=
  flagAverage p (conditional (G := G) f)

/-- Finite canonical two-time Harris inequality. Both conditional Haar association
and decreasingness in the refresh flags are proved above. -/
theorem canonical_association [DistribLattice X] [Nonempty X]
    (hact : ∀ g : G, Monotone (fun x : X => g • x))
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (f h : (B → X) → ℝ) (hf0 : ∀ ω, 0 ≤ f ω) (hh0 : ∀ ω, 0 ≤ h ω)
    (hf : Monotone f) (hh : Monotone h) :
    canonical (G := G) p f * canonical (G := G) p h ≤
      canonical (G := G) p (fun ω => f ω * h ω) := by
  refine (flag_harris_antitone p hp0 hp1 _ _ (conditional_nonneg f)
    (conditional_nonneg h) (conditional_antitone f) (conditional_antitone h)).trans ?_
  exact flagAverage_mono p hp0 hp1 (conditional_association hact f h hf0 hh0 hf hh)

theorem canonical_square_lower [Nonempty X]
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) (f : (B → X) → ℝ) :
    (average f)^2 ≤ canonical (G := G) p f := by
  rw [← flagAverage_const p ((average f)^2)]
  exact flagAverage_mono p hp0 hp1 (conditional_square_lower f)

/-- Two-time probability of a duplicated event under independent block refresh. -/
noncomputable def canonicalProbability (p : B → ℝ) (A : Set (B → X)) : ℝ :=
  canonical (G := G) p (eventIndicator A)

/-- Explicit finite law: independent Bernoulli flags, independent uniform group
elements, and an independent uniform initial configuration. -/
theorem canonicalProbability_eq (p : B → ℝ) (A : Set (B → X)) :
    canonicalProbability (G := G) p A =
      ∑ s : B → Bool, (∏ b, if s b then p b else 1 - p b) *
        average (fun g : B → G => average (fun ω : B → X =>
          if ω ∈ A ∧ refresh s g ω ∈ A then (1 : ℝ) else 0)) := by
  unfold canonicalProbability canonical flagAverage flagWeight
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  let := maskedAction (G := G) (X := X) s
  exact duplicateProbability_eq A

/-- Duplicated Harris for increasing events under the finite block refresh law. -/
theorem canonical_event_association [DistribLattice X] [Nonempty X]
    (hact : ∀ g : G, Monotone (fun x : X => g • x))
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (A D : Set (B → X)) (hA : IsUpperSet A) (hD : IsUpperSet D) :
    canonicalProbability (G := G) p A * canonicalProbability (G := G) p D ≤
      canonicalProbability (G := G) p (A ∩ D) := by
  unfold canonicalProbability
  rw [eventIndicator_inter]
  exact canonical_association hact p hp0 hp1 _ _ (eventIndicator_nonneg A)
    (eventIndicator_nonneg D) (eventIndicator_monotone A hA) (eventIndicator_monotone D hD)

theorem canonical_event_square_lower [Nonempty X]
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) (A : Set (B → X)) :
    (average (eventIndicator A))^2 ≤ canonicalProbability (G := G) p A :=
  canonical_square_lower p hp0 hp1 _

section Coordinates

variable {J : Type*} [Fintype J] [MulAction G J]

/-- Canonical block refresh on Boolean coordinates: each block is a `J`-cube. -/
noncomputable def blockCoordinateProbability (p : B → ℝ) (A : Set (B → J → Bool)) : ℝ :=
  letI := coordinateAction (G := G) (I := J)
  canonicalProbability (G := G) p A

/-- Finite canonical duplicated Harris for arbitrary coordinate groups on disjoint blocks,
including the full permutation group and two-site blocks. -/
theorem block_coordinate_harris
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (A D : Set (B → J → Bool)) (hA : IsUpperSet A) (hD : IsUpperSet D) :
    blockCoordinateProbability (G := G) p A * blockCoordinateProbability (G := G) p D ≤
      blockCoordinateProbability (G := G) p (A ∩ D) := by
  let := coordinateAction (G := G) (I := J)
  apply canonical_event_association _ p hp0 hp1 A D hA hD
  intro g ω η hωη j
  exact hωη (g⁻¹ • j)

theorem block_coordinate_square_lower
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) (A : Set (B → J → Bool)) :
    (average (eventIndicator A))^2 ≤ blockCoordinateProbability (G := G) p A := by
  let := coordinateAction (G := G) (I := J)
  exact canonical_event_square_lower p hp0 hp1 A

/-- The common-refresh-probability form of finite canonical duplicated Harris. -/
theorem finite_block_harris (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A D : Set (B → J → Bool)) (hA : IsUpperSet A) (hD : IsUpperSet D) :
    blockCoordinateProbability (G := G) (fun _ => p) A *
        blockCoordinateProbability (G := G) (fun _ => p) D ≤
      blockCoordinateProbability (G := G) (fun _ => p) (A ∩ D) :=
  block_coordinate_harris _ (fun _ => hp0) (fun _ => hp1) A D hA hD

end Coordinates

#print axioms canonical_association
#print axioms canonical_square_lower
#print axioms conditional_antitone
#print axioms flagWeight_sum
#print axioms canonicalProbability_eq
#print axioms block_coordinate_harris
#print axioms block_coordinate_square_lower

end ExceptionalTimes.CanonicalHarris
