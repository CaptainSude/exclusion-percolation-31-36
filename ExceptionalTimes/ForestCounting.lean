import ExceptionalTimes.ForestIntegration
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
The finite combinatorial cost of the centered-block forest expansion.
Only eligible forests need to be integrated. Counting all edge subsets gives
an overcount, which is proved here, followed by the binomial, factorial, and
supergeometric summation estimates. No percolation probability bound is assumed.
-/

open scoped BigOperators Classical
open Filter

namespace ExceptionalTimes.ForestCounting

/-- An unordered graph edge is recorded once, in increasing endpoint order. -/
noncomputable def forwardEdges {N : ℕ} (G : SimpleGraph (Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

theorem forwardEdges_injective (N : ℕ) :
    Function.Injective (@forwardEdges N) := by
  intro G H h
  apply SimpleGraph.ext
  funext u v
  apply propext
  by_cases huv : u < v
  · have hm := congrArg (fun s : Finset (Fin N × Fin N) => (u, v) ∈ s) h
    simpa [forwardEdges, huv] using hm
  · by_cases he : u = v
    · subst v
      simp
    · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm he)
      have hm := congrArg (fun s : Finset (Fin N × Fin N) => (v, u) ∈ s) h
      simpa [forwardEdges, hvu, G.adj_comm, H.adj_comm] using hm

/-- Any finite family of eligible forests with `j` edges is bounded by the
number of `j`-subsets of the square endpoint set. Acyclicity is not needed for
this overcount and is never supplied as an integration premise for extra graphs. -/
theorem forest_family_card_le (N j : ℕ) (family : Finset (SimpleGraph (Fin N)))
    (hcard : ∀ G ∈ family, (forwardEdges G).card = j) :
    family.card ≤ (N ^ 2).choose j := by
  have hsub : family.image forwardEdges ⊆ Finset.univ.powersetCard j := by
    intro s hs
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard G hG⟩
  have h := Finset.card_le_card hsub
  simpa [Finset.card_image_of_injective family (forwardEdges_injective N),
    Finset.card_powersetCard, Fintype.card_prod, pow_two] using h

noncomputable def binomialWeight (N k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (N.choose j : ℝ) * z ^ j

/-- A partial nonnegative binomial sum is bounded by the full binomial sum. -/
theorem binomialWeight_le {N k : ℕ} (hk : k ≤ N) {z : ℝ} (hz : 0 ≤ z) :
    binomialWeight N k z ≤ (1 + z) ^ N := by
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * z ^ j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.add_le_add_right hk 1)
      · intro j _ _
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)
    _ = _ := by
      rw [show (1 + z) ^ N = (z + 1) ^ N by rw [add_comm 1 z], add_pow]
      simp only [one_pow, mul_one]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The forest binomial factor has only exponential growth in the number of
anchors, when the number `J` of fixed roots is fixed. -/
theorem forest_binomial_bound (k J : ℕ) (hk : 1 ≤ k) :
    binomialWeight ((k + J) ^ 2) k (1 / (k : ℝ)) ≤
      (Real.exp (((J : ℝ) + 1) ^ 2)) ^ k := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkN : k ≤ (k + J) ^ 2 := (Nat.le_add_right k J).trans
    (by simpa [pow_two] using Nat.le_mul_self (k + J))
  have hlen : (k : ℝ) + J ≤ ((J : ℝ) + 1) * k := by
    nlinarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hsquare : ((k : ℝ) + J) ^ 2 ≤ (((J : ℝ) + 1) * k) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlen 2
  calc
    _ ≤ (1 + 1 / (k : ℝ)) ^ ((k + J) ^ 2) :=
      binomialWeight_le hkN (by positivity)
    _ ≤ (Real.exp (1 / (k : ℝ))) ^ ((k + J) ^ 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (k : ℝ))]) _
    _ = Real.exp ((((k + J) ^ 2 : ℕ) : ℝ) / k) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp ((((J : ℝ) + 1) ^ 2) * k) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_iff₀ hk0).mpr
      push_cast
      nlinarith
    _ = _ := by rw [mul_comm, Real.exp_nat_mul]

/-- The needed factorial bound follows directly from a positive term of the
exponential series; no asymptotic Stirling estimate is assumed. -/
theorem factorial_ratio_le_exp (k : ℕ) :
    (k : ℝ) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1) ^ k := by
  simpa only [← Real.exp_nat_mul, mul_one] using
    Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k

theorem power_factorial_split (k : ℕ) (hk : 1 ≤ k) (β : ℝ) :
    (k : ℝ) ^ ((1 - β) * k) / (k.factorial : ℝ) =
      ((k : ℝ) ^ k / (k.factorial : ℝ)) * (k : ℝ) ^ (-β * k) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  rw [show (1 - β) * (k : ℝ) = (k : ℝ) + (-β * k) by ring,
    Real.rpow_add hk0, Real.rpow_natCast]
  ring

/-- The complete scalar majorant produced by the short-edge decomposition. -/
noncomputable def forestMajorant (J : ℕ) (β : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) ^ ((1 - β) * k) / (k.factorial : ℝ)) *
    binomialWeight ((k + J) ^ 2) k (1 / (k : ℝ))

/-- Binomial counting and the factorial convert the leaf-integral estimate
into the exact supergeometric shape required by the block expansion. -/
theorem forestMajorant_le (J k : ℕ) (hk : 1 ≤ k) (β : ℝ) :
    forestMajorant J β k ≤
      (Real.exp 1 * Real.exp (((J : ℝ) + 1) ^ 2)) ^ k * (k : ℝ) ^ (-β * k) := by
  unfold forestMajorant
  rw [power_factorial_split k hk β]
  calc
    _ ≤ (((Real.exp 1) ^ k) * (k : ℝ) ^ (-β * k)) *
        binomialWeight ((k + J) ^ 2) k (1 / (k : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (factorial_ratio_le_exp k) (by positivity))
      unfold binomialWeight
      positivity
    _ ≤ (((Real.exp 1) ^ k) * (k : ℝ) ^ (-β * k)) *
        (Real.exp (((J : ℝ) + 1) ^ 2)) ^ k :=
      mul_le_mul_of_nonneg_left (forest_binomial_bound k J hk) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem superfactor_eq_pow (A β : ℝ) (k : ℕ) :
    A ^ k * (k : ℝ) ^ (-β * k) = (A * (k : ℝ) ^ (-β)) ^ k := by
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg k)]

/-- The resulting coefficient majorant is summable for every positive loss
exponent, even after any fixed exponential factor. -/
theorem summable_superfactor {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β) :
    Summable (fun k : ℕ => A ^ k * (k : ℝ) ^ (-β * k)) := by
  have ht : Tendsto (fun k : ℕ => A * (k : ℝ) ^ (-β)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop).const_mul A
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).of_norm_bounded_eventually_nat
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), superfactor_eq_pow]
  exact pow_le_pow_left₀ (by positivity) hk.le k

/-- The precise short-edge scale calculation from the forest expansion. -/
theorem short_edge_factor (k j : ℕ) (hk : 1 ≤ k) (hj : j ≤ k) (g : ℝ) :
    (k : ℝ) ^ (g * (k - j : ℕ) / 2) *
        ((k : ℝ) ^ (-(1 / 2 : ℝ))) ^ ((2 - g) * j) =
      (k : ℝ) ^ (g * k / 2) * (1 / (k : ℝ)) ^ j := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hinv : (1 / (k : ℝ)) ^ j = (k : ℝ) ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg hk0.le, Real.rpow_natCast]
    simp
  rw [hinv, ← Real.rpow_mul hk0.le, ← Real.rpow_add hk0, ← Real.rpow_add hk0,
    Nat.cast_sub hj]
  congr 1
  ring

theorem short_edge_sum_eq (k J : ℕ) (hk : 1 ≤ k) (g : ℝ) :
    (∑ j ∈ Finset.range (k + 1), (k : ℝ) ^ (g * (k - j : ℕ) / 2) *
      (((k + J) ^ 2).choose j : ℝ) *
      ((k : ℝ) ^ (-(1 / 2 : ℝ))) ^ ((2 - g) * j)) =
    (k : ℝ) ^ (g * k / 2) * binomialWeight ((k + J) ^ 2) k (1 / (k : ℝ)) := by
  unfold binomialWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ = (((k + J) ^ 2).choose j : ℝ) *
        ((k : ℝ) ^ (g * (k - j : ℕ) / 2) *
          ((k : ℝ) ^ (-(1 / 2 : ℝ))) ^ ((2 - g) * j)) := by ring
    _ = _ := by rw [short_edge_factor k j hk hjk g]; ring

/-- The entire finite sum in the forest integral estimate, including its
factorial, has the manuscript's claimed exponent. -/
theorem short_edge_sum_bound (k J : ℕ) (hk : 1 ≤ k) (g : ℝ) :
    (1 / (k.factorial : ℝ)) *
      (∑ j ∈ Finset.range (k + 1), (k : ℝ) ^ (g * (k - j : ℕ) / 2) *
        (((k + J) ^ 2).choose j : ℝ) *
        ((k : ℝ) ^ (-(1 / 2 : ℝ))) ^ ((2 - g) * j)) ≤
      (Real.exp 1 * Real.exp (((J : ℝ) + 1) ^ 2)) ^ k *
        (k : ℝ) ^ (-(1 - g / 2) * k) := by
  rw [short_edge_sum_eq k J hk g]
  convert forestMajorant_le J k hk (1 - g / 2) using 1
  unfold forestMajorant
  rw [show (1 - (1 - g / 2)) * (k : ℝ) = g * k / 2 by ring]
  ring

/-- Arbitrary exponential prefactors preserve summability of the actual
binomial/factorial majorant, not just of a proposed asymptotic formula. -/
theorem summable_forestMajorant (J : ℕ) {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) :
    Summable (fun k : ℕ => C ^ k * forestMajorant J β k) := by
  let A : ℝ := Real.exp 1 * Real.exp (((J : ℝ) + 1) ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply (summable_superfactor (mul_nonneg hC hA) hβ).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hnonneg : 0 ≤ C ^ k * forestMajorant J β k := by
    unfold forestMajorant binomialWeight
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    _ ≤ C ^ k * (A ^ k * (k : ℝ) ^ (-β * k)) :=
      mul_le_mul_of_nonneg_left (forestMajorant_le J k hk β) (pow_nonneg hC _)
    _ = _ := by rw [mul_pow]; ring

#print axioms forest_family_card_le
#print axioms forestMajorant_le
#print axioms summable_superfactor
#print axioms short_edge_sum_bound
#print axioms summable_forestMajorant

end ExceptionalTimes.ForestCounting
