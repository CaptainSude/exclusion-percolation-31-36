import ExceptionalTimes.OrderedDimerCoefficients
import ExceptionalTimes.ForestBadLocation

/-! Counting and bad-set restriction for actual ordered selections.
Repeated tuples are used only in nonnegative upper bounds. -/
open scoped Classical BigOperators
namespace ExceptionalTimes.OrderedTupleMass
noncomputable section
set_option backward.isDefEq.respectTransparency false
open InsertionCounting PairSquareSewing LatticeRadial

variable {B : Type*} [Fintype B]

def badOrders (k : ℕ) (bad : Finset (Fin k→B)) : Finset (OrderedSelections B k) :=
  Finset.univ.filter (fun o => anchorTuple o∈bad)

theorem mem_badOrders (k : ℕ) (bad : Finset (Fin k→B)) (o : OrderedSelections B k) :
    o∈badOrders k bad ↔ anchorTuple o∈bad := by simp [badOrders]

theorem bad_sum_le_tuple_sum (k : ℕ) (bad : Finset (Fin k→B))
    (f : OrderedSelections B k→ℝ) (bound : (Fin k→B)→ℝ)
    (hbound0 : ∀x,0≤bound x) (hbound : ∀o,f o≤bound (anchorTuple o)) :
    (∑o∈badOrders k bad,f o)≤∑x∈bad,bound x := by
  apply Finset.sum_le_sum_of_injOn anchorTuple
  · intro o _ p _ h
    exact anchorTuple_injective k h
  · intro x hx
    obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_badOrders k bad o).mp ho
  · intro o _
    exact hbound o
  · intro x _ _
    exact hbound0 x

theorem scaled_ordered_mass (k : ℕ) (s : Finset Site) {ε r : ℝ} (center : ℂ)
    (hε : 0<ε) (hr : ε≤r) (hs : ∀v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*(Fintype.card (OrderedSelections s k):ℝ)≤(121*r^2)^k := by
  have hc : (Fintype.card (OrderedSelections s k):ℝ)≤(s.card:ℝ)^k := by
    have ht := Fintype.card_le_of_injective (anchorTuple (B:=s) (k:=k)) (anchorTuple_injective k)
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow] using
      (show (Fintype.card (OrderedSelections s k):ℝ)≤Fintype.card (Fin k→s) by exact_mod_cast ht)
  have hm := scaled_ball_mass_le s hε hr center hs
  calc
    _≤ε^(2*k)*(s.card:ℝ)^k := mul_le_mul_of_nonneg_left hc (by positivity)
    _=(ε^2*(s.card:ℝ))^k := by rw [mul_pow,pow_mul]
    _≤_ := pow_le_pow_left₀ (by positivity) hm k

#print axioms bad_sum_le_tuple_sum
#print axioms scaled_ordered_mass
end
end ExceptionalTimes.OrderedTupleMass
