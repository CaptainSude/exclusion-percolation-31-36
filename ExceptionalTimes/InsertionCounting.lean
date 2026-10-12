import ExceptionalTimes.ExpansionLimit
import Mathlib.Data.Fintype.Perm

/-! The factorial in the insertion expansion is exact. Every k-element
selection has precisely k! orderings, which inject into all anchor tuples. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.InsertionCounting

variable {B : Type*} [Fintype B]

abbrev Selections (B : Type*) [Fintype B] (k : ℕ) := {S : Finset B // S.card=k}
abbrev OrderedSelections (B : Type*) [Fintype B] (k : ℕ) :=
  Σ S : Selections B k, Fin k ≃ S.val

def anchorTuple {k : ℕ} (o : OrderedSelections B k) : Fin k → B :=
  fun i => (o.2 i).val

theorem anchorTuple_injective (k : ℕ) : Function.Injective (anchorTuple (B := B) (k := k)) := by
  rintro ⟨⟨S,hS⟩,e⟩ ⟨⟨T,hT⟩,f⟩ h
  have hST : S=T := by
    ext b
    constructor
    · intro hb
      obtain ⟨i,hi⟩ := e.surjective ⟨b,hb⟩
      have hh := congrFun h i
      change (e i).val=(f i).val at hh
      rw [hi] at hh
      have heq : b=(f i).val := hh
      rw [heq]
      exact (f i).property
    · intro hb
      obtain ⟨i,hi⟩ := f.surjective ⟨b,hb⟩
      have hh := congrFun h i
      change (e i).val=(f i).val at hh
      rw [hi] at hh
      have heq : (e i).val=b := hh
      rw [←heq]
      exact (e i).property
  subst T
  have hef : e=f := by
    ext i
    exact congrFun h i
  cases hef
  rfl

theorem ordered_sum_eq_factorial (k : ℕ) (f : Finset B → ℝ) :
    (∑ o : OrderedSelections B k,f o.1.val)=
      (k.factorial : ℝ)*∑ S : Selections B k,f S.val := by
  rw [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have hc : Fintype.card (Fin k ≃ S.val)=k.factorial := by
    simpa using Fintype.card_equiv (Finset.equivFinOfCardEq S.property).symm
  simp [hc]

/-- The bound can depend on the order of the anchors. It only has to bound
the same selected coefficient for every ordering. Repeated anchors appear
only on the nonnegative upper side. -/
theorem selection_sum_le_tuple_sum (k : ℕ) (f : Finset B → ℝ)
    (bound : (Fin k → B) → ℝ) (hbound0 : ∀ x,0≤bound x)
    (hbound : ∀ o : OrderedSelections B k,f o.1.val≤bound (anchorTuple o)) :
    (k.factorial : ℝ)*∑ S : Selections B k,f S.val≤∑ x : Fin k → B,bound x := by
  rw [←ordered_sum_eq_factorial]
  apply (Finset.sum_le_sum (fun o _ => hbound o)).trans
  exact Finset.sum_le_sum_of_injOn anchorTuple
    (fun _ _ _ _ h => anchorTuple_injective k h)
    (Finset.subset_univ _) (fun _ _ => le_rfl) (fun x _ _ => hbound0 x)

theorem coefficient_selection_sum {H : B → Type*} [∀ b,Fintype (H b)]
    (p u : ∀ b,H b → ℝ) (f : (∀ b,H b) → ℝ) (k : ℕ) :
    ExpansionLimit.coefficient p u f k=
      ∑ S : Selections B k,BlockExpansion.selectedKernel p u S.val f := by
  unfold ExpansionLimit.coefficient
  exact Finset.sum_subtype _ (by intro S; simp) _

theorem coefficient_le_tuple_sum {H : B → Type*} [∀ b,Fintype (H b)]
    (p u : ∀ b,H b → ℝ) (f : (∀ b,H b) → ℝ) (k : ℕ)
    (bound : (Fin k → B) → ℝ) (hbound0 : ∀ x,0≤bound x)
    (hbound : ∀ o : OrderedSelections B k,
      |BlockExpansion.selectedKernel p u o.1.val f|≤bound (anchorTuple o)) :
    |ExpansionLimit.coefficient p u f k|≤
      (∑ x : Fin k → B,bound x)/(k.factorial : ℝ) := by
  have hfac : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  apply (le_div_iff₀ hfac).mpr
  rw [mul_comm,coefficient_selection_sum]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hfac.le)
  exact selection_sum_le_tuple_sum k (fun S => |BlockExpansion.selectedKernel p u S f|)
    bound hbound0 hbound

#print axioms coefficient_le_tuple_sum

end ExceptionalTimes.InsertionCounting


