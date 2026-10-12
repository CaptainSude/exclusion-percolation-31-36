import ExceptionalTimes.Model
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The axial integer-coordinate graph is the usual Euclidean triangular
lattice: its six neighbors are exactly the distinct lattice points at
Euclidean distance one. This is part of the model dictionary needed for
published planar percolation results. It asserts no percolation estimate.
-/

set_option autoImplicit false
open scoped ComplexConjugate

namespace ExceptionalTimes

/-- The positive definite integral quadratic form of the triangular lattice. -/
def triangularNormForm (v : Site) : ℤ := v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2

theorem triangularNormForm_eq_one_iff (x y : ℤ) :
    x ^ 2 + x * y + y ^ 2 = 1 ↔
      (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨
      (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨
      (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1) := by
  constructor
  · intro h
    have hx : 3 * x ^ 2 ≤ 4 := by nlinarith [sq_nonneg (x + 2 * y)]
    have hy : 3 * y ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * x + y)]
    have hx2 : x ^ 2 ≤ 1 := by omega
    have hy2 : y ^ 2 ≤ 1 := by omega
    have hxlo : -1 ≤ x := by nlinarith
    have hxhi : x ≤ 1 := by nlinarith
    have hylo : -1 ≤ y := by nlinarith
    have hyhi : y ≤ 1 := by nlinarith
    interval_cases x <;> interval_cases y <;> norm_num at *
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem triangularAdj_iff_normForm (u v : Site) :
    TriangularAdj u v ↔ triangularNormForm (v - u) = 1 := by
  rw [triangularNormForm, triangularNormForm_eq_one_iff]
  simp only [Prod.fst_sub, Prod.snd_sub]
  unfold TriangularAdj
  omega

/-- The embedding x + y exp(i*pi/3), expressed without trigonometric choices. -/
noncomputable def triangularEmbedding (v : Site) : ℂ :=
  ⟨(v.1 : ℝ) + (v.2 : ℝ) / 2, Real.sqrt 3 * (v.2 : ℝ) / 2⟩

@[simp] theorem triangularEmbedding_sub (u v : Site) :
    triangularEmbedding (u - v) = triangularEmbedding u - triangularEmbedding v := by
  apply Complex.ext <;> simp [triangularEmbedding] <;> ring

theorem triangularEmbedding_normSq (v : Site) :
    Complex.normSq (triangularEmbedding v) = (triangularNormForm v : ℝ) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [triangularEmbedding, Complex.normSq_apply, triangularNormForm,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  nlinarith [sq_nonneg (v.2 : ℝ)]

theorem triangularEmbedding_injective : Function.Injective triangularEmbedding := by
  intro u v h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  dsimp [triangularEmbedding] at hre him
  have hy : (u.2 : ℝ) = (v.2 : ℝ) := by nlinarith
  have hx : (u.1 : ℝ) = (v.1 : ℝ) := by linarith
  exact Prod.ext (Int.cast_injective hx) (Int.cast_injective hy)

/-- The intended nearest-neighbor graph is exactly unit-distance adjacency
in the embedded triangular lattice, with the genuine complex-plane metric. -/
theorem triangularAdj_iff_euclidean_distance (u v : Site) :
    TriangularAdj u v ↔ dist (triangularEmbedding u) (triangularEmbedding v) = 1 := by
  rw [triangularAdj_iff_normForm, dist_comm, Complex.dist_eq,
    ← triangularEmbedding_sub]
  have hs := triangularEmbedding_normSq (v - u)
  rw [Complex.normSq_eq_norm_sq] at hs
  constructor
  · intro h
    rw [h] at hs
    rw [Int.cast_one] at hs
    nlinarith [norm_nonneg (triangularEmbedding (v - u))]
  · intro h
    rw [h] at hs
    exact_mod_cast hs.symm

/-- Fixed-ratio comparison with axial coordinates, independently of any
percolation estimate or choice of the outer box convention. -/
theorem triangularEmbedding_coordinate_bounds (v : Site) :
    |(v.1 : ℝ)| ≤ 2 * ‖triangularEmbedding v‖ ∧
      |(v.2 : ℝ)| ≤ 2 * ‖triangularEmbedding v‖ := by
  have hs := triangularEmbedding_normSq v
  rw [Complex.normSq_eq_norm_sq] at hs
  simp only [triangularNormForm, Int.cast_add, Int.cast_mul, Int.cast_pow] at hs
  have hn := norm_nonneg (triangularEmbedding v)
  constructor
  · nlinarith [sq_nonneg ((v.1 : ℝ) + 2 * (v.2 : ℝ)),
      sq_abs (v.1 : ℝ), abs_nonneg (v.1 : ℝ)]
  · nlinarith [sq_nonneg (2 * (v.1 : ℝ) + (v.2 : ℝ)),
      sq_abs (v.2 : ℝ), abs_nonneg (v.2 : ℝ)]

theorem triangularEmbedding_norm_le_coordinates (v : Site) :
    ‖triangularEmbedding v‖ ≤ |(v.1 : ℝ)| + |(v.2 : ℝ)| := by
  have hs := triangularEmbedding_normSq v
  rw [Complex.normSq_eq_norm_sq] at hs
  simp only [triangularNormForm, Int.cast_add, Int.cast_mul, Int.cast_pow] at hs
  have hprod := le_abs_self ((v.1 : ℝ) * (v.2 : ℝ))
  rw [abs_mul] at hprod
  nlinarith [sq_abs (v.1 : ℝ), sq_abs (v.2 : ℝ), abs_nonneg (v.1 : ℝ),
    abs_nonneg (v.2 : ℝ), mul_nonneg (abs_nonneg (v.1 : ℝ)) (abs_nonneg (v.2 : ℝ))]

theorem triangularEmbedding_norm_le_of_mem_box {v : Site} {n : ℕ}
    (hv : v ∈ latticeBox n) : ‖triangularEmbedding v‖ ≤ 2 * (n : ℝ) := by
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc] at hv
  have hx : |(v.1 : ℝ)| ≤ (n : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast hv.1.1
    · exact_mod_cast hv.1.2
  have hy : |(v.2 : ℝ)| ≤ (n : ℝ) := by
    apply abs_le.mpr
    constructor
    · exact_mod_cast hv.2.1
    · exact_mod_cast hv.2.2
  linarith [triangularEmbedding_norm_le_coordinates v]

theorem mem_box_of_triangularEmbedding_norm_le {v : Site} {n : ℕ}
    (hv : ‖triangularEmbedding v‖ ≤ (n : ℝ)) : v ∈ latticeBox (2 * n) := by
  obtain ⟨hx, hy⟩ := triangularEmbedding_coordinate_bounds v
  have hx' : |(v.1 : ℝ)| ≤ 2 * (n : ℝ) := hx.trans (by linarith)
  have hy' : |(v.2 : ℝ)| ≤ 2 * (n : ℝ) := hy.trans (by linarith)
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor
  · exact_mod_cast (abs_le.mp hx').1
  · exact_mod_cast (abs_le.mp hx').2
  · exact_mod_cast (abs_le.mp hy').1
  · exact_mod_cast (abs_le.mp hy').2

/-- Connection beyond a genuine Euclidean disk in the embedded lattice. -/
def EuclideanOneArm (ω : Configuration) (v : Site) (r : ℝ) : Prop :=
  ∃ w ∈ BlackCluster ω v, r < ‖triangularEmbedding w‖

theorem euclideanOneArm_implies_oneArm {ω : Configuration} {v : Site} {n : ℕ}
    (h : EuclideanOneArm ω v (2 * (n : ℝ))) : OneArm ω v n := by
  obtain ⟨w, hw, hn⟩ := h
  exact ⟨w, hw, fun hbox => (not_lt_of_ge
    (triangularEmbedding_norm_le_of_mem_box hbox)) hn⟩

theorem oneArm_implies_euclideanOneArm {ω : Configuration} {v : Site} {n : ℕ}
    (h : OneArm ω v (2 * n)) : EuclideanOneArm ω v (n : ℝ) := by
  obtain ⟨w, hw, hn⟩ := h
  refine ⟨w, hw, lt_of_not_ge ?_⟩
  intro hnorm
  exact hn (mem_box_of_triangularEmbedding_norm_le hnorm)

end ExceptionalTimes

#print axioms ExceptionalTimes.triangularEmbedding_injective
#print axioms ExceptionalTimes.triangularAdj_iff_euclidean_distance
#print axioms ExceptionalTimes.triangularEmbedding_coordinate_bounds
#print axioms ExceptionalTimes.triangularEmbedding_norm_le_coordinates
#print axioms ExceptionalTimes.oneArm_implies_euclideanOneArm
