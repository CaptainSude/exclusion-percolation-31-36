import ExceptionalTimes.ArmEnlargement
import ExceptionalTimes.ForestTelescope

/-! Product of local arm weights on the actual positive lives. The only static
inputs are local arm-ratio and power estimates; the forest, life dictionary,
count, logarithmic charge, and telescoping are all constructed and proved. -/

open scoped BigOperators Classical
open Set
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestArmWeights

noncomputable local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

open ArmEnlargement ForestDiameterLoss ForestProbes ForestTelescope KruskalLives
open ForestLifeGeometry ForestGeometry RootKruskal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def lifeCost {V : Type*} [Fintype V] (fixed : V → Prop) (position : V → X)
    (cutoff stop margin : ℝ) (α : ℝ → ℝ → ℝ) (S : Set V) : ℝ :=
  separatedArmCost α
    (8 * max (birth fixed position cutoff stop S) (span fixed position cutoff S + 2*margin))
    (death fixed position cutoff stop S / 8)

/-- Actual finite forest arm product, with every diameter loss paid for.
The static profile is extended without zeros outside its geometric range. -/
theorem actual_forest_arm_product (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (position : Fin (k+J) → X)
    {cutoff stop margin C Q g : ℝ} (hb : 0 < cutoff) (hcut : cutoff ≤ stop)
    (hm : 0 ≤ margin) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hg : 0 ≤ g)
    (α : ℝ → ℝ → ℝ) (hα : ∀ a b, 0 ≤ α a b) (p : ℝ → ℝ)
    (hpnz : ∀ t, p t ≠ 0) (hstop : p stop = 1)
    (hp : ∀ t, 0 < t → t ≤ stop → 0 < p t)
    (hquasi : ∀ a b, 0 < a → a < b → b ≤ stop → α a b ≤ Q * (p a / p b))
    (hlower : ∀ a b, 0 < a → a ≤ b → b ≤ stop → p b ≤ C * (b/a)^g * p a) :
    (∏ S ∈ positiveLives fixed position cutoff stop, lifeCost fixed position cutoff stop margin α S) ≤
      ((Q*C^2*256^g)^2 * Real.exp (g*(1+4*margin/cutoff)))^k *
        (p cutoff^k /
          ∏ e ∈ (recorded fixed position cutoff ⊓ threshold position cutoff stop).edgeFinset,
            p (clippedEdgeLength position cutoff e)) := by
  let L := positiveLives fixed position cutoff stop
  let K := Q*C^2*256^g
  let loss := fun S => logarithmicLoss (birth fixed position cutoff stop S)
    (death fixed position cutoff stop S) (span fixed position cutoff S + 2*margin)
  let ratio := fun S => p (birth fixed position cutoff stop S) / p (death fixed position cutoff stop S)
  have hspec := fun S (hS : S ∈ L) => positiveLives_spec fixed position cutoff stop hS
  have hrpos : ∀ S ∈ L, 0 ≤ ratio S := by
    intro S hS
    have h := hspec S hS
    have hu := hb.trans_le (cutoff_le_birth h.1)
    have hv := hu.trans h.2.2
    exact div_nonneg (hp _ hu (h.2.2.le.trans (death_le_stop h.1))).le
      (hp _ hv (death_le_stop h.1)).le
  have hK : 1 ≤ K := by
    have hpw : (1:ℝ) ≤ 256^g := Real.one_le_rpow (by norm_num) hg
    have hc2 : (1:ℝ) ≤ C^2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hQ hc2) hpw
  have hbound : (∏ S ∈ L, lifeCost fixed position cutoff stop margin α S) ≤
      K^L.card * Real.exp (g * ∑ S ∈ L, loss S) * ∏ S ∈ L, ratio S := by
    calc
      _ ≤ ∏ S ∈ L, K * Real.exp (g*loss S) * ratio S := by
        apply Finset.prod_le_prod₀
        · intro S _hS
          exact separatedArmCost_nonneg α hα _ _
        · intro S hS
          have h := hspec S hS
          exact buffered_armCost_le α p (hb.trans_le (cutoff_le_birth h.1)) h.2.2.le
            (death_le_stop h.1) hC hQ hg hp hquasi hlower
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          ← Real.exp_sum, ← Finset.mul_sum]
  have hcount : K^L.card ≤ K^(2*k) :=
    pow_le_pow_right₀ hK (positiveLives_card_le k J fixed hroots position cutoff stop)
  have hcharge : Real.exp (g * ∑ S ∈ L, loss S) ≤
      Real.exp (g*(1+4*margin/cutoff))^k := by
    have h := exponential_loss_le k J fixed hroots position (margin := 2*margin) hb
      (mul_nonneg (by norm_num) hm) hg L
      (fun S hS => (hspec S hS).1) (fun S hS => (hspec S hS).2.1)
      (fun S hS => (hspec S hS).2.2)
    simpa only [show (2:ℝ)*(2*margin) = 4*margin by ring] using h
  have hprod : 0 ≤ ∏ S ∈ L, ratio S := Finset.prod_nonneg hrpos
  have htel := actual_forest_telescope fixed position cutoff stop hcut p hpnz hstop
  have hfree : Fintype.card {a // ¬ fixed a} = k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hroots]
    omega
  rw [hfree] at htel
  calc
    _ ≤ K^L.card * Real.exp (g * ∑ S ∈ L, loss S) * ∏ S ∈ L, ratio S := hbound
    _ ≤ K^(2*k) * Real.exp (g*(1+4*margin/cutoff))^k * ∏ S ∈ L, ratio S :=
      mul_le_mul_of_nonneg_right (mul_le_mul hcount hcharge (Real.exp_nonneg _) (by positivity)) hprod
    _ = _ := by
      have hc : K^(2*k) * Real.exp (g*(1+4*margin/cutoff))^k =
          ((Q*C^2*256^g)^2 * Real.exp (g*(1+4*margin/cutoff)))^k := by
        rw [pow_mul, ← mul_pow]
      apply congrArg₂ (fun a b : ℝ => a*b) hc
      dsimp only [L, ratio]
      exact htel

#print axioms actual_forest_arm_product

end ExceptionalTimes.ForestArmWeights
