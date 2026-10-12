import ExceptionalTimes.EnvironmentVariance
import ExceptionalTimes.SignedResponse
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp

/-!
# Elimination of a common mesoscopic square

This file proves algebra and an iterated-limit implication. The two
pair/square error bounds are hypotheses, not conclusions about percolation.
In particular, it does not replace the fixed square radius by a mesh-dependent
radius or assume a two-microscopic-probe sewing theorem.
-/

open Filter
open scoped Topology

namespace ExceptionalTimes.CommonSquare

/-- Integration against `(δ₀₁ + δ₁₀ - δ₀₀ - δ₁₁) / 4`. -/
noncomputable def response (F : Bool → Bool → ℝ) : ℝ :=
  (F false true + F true false - F false false - F true true) / 4

theorem response_const (c : ℝ) : response (fun _ _ => c) = 0 := by
  unfold response
  ring

theorem response_eq_bitResponse (test : Bool × Bool → ℝ) :
    response (fun a b => test (a, b)) = SignedResponse.bitResponse test := rfl

noncomputable def oneTimeDifference (φ : Bool → Bool) : ℝ :=
  (if φ true then 1 else 0) - (if φ false then 1 else 0)

noncomputable def squareJumpResponse (φ : Bool → Bool) : ℝ :=
  response (fun a b => if φ a = φ b then 0 else 1)

/-- The square has the same universal signed history law as either pair
rule, with amplitude its one-time pivotal response. This identity holds
for every real exterior test, not only the crossing-jump calibrator. -/
theorem square_pushforward (φ : Bool → Bool) (hφ : Monotone φ)
    (test : Bool × Bool → ℝ) :
    response (fun a b => test (φ a, φ b)) =
      oneTimeDifference φ * SignedResponse.bitResponse test := by
  have hm := hφ (show false ≤ true by decide)
  cases h0 : φ false <;> cases h1 : φ true <;>
    simp_all [response, oneTimeDifference, SignedResponse.bitResponse]
  exact False.elim ((show ¬ (true ≤ false) by decide) hm)

/-- A monotone crossing controlled by one forced bit has jump response
exactly half of its one-time signed response. This fixes the normalization
between the released source's `D_e(h)` and the common jump calibrator. -/
theorem squareJumpResponse_eq_half (φ : Bool → Bool) (hφ : Monotone φ) :
    squareJumpResponse φ = oneTimeDifference φ / 2 := by
  have hm := hφ (show false ≤ true by decide)
  cases h0 : φ false <;> cases h1 : φ true <;>
    simp_all [squareJumpResponse, response, oneTimeDifference]
  · norm_num
  · exact False.elim ((show ¬ (true ≤ false) by decide) hm)

/-- The factor of two survives averaging over every finite exterior law. -/
theorem expected_squareJumpResponse_eq_half {Ω : Type*} [Fintype Ω]
    (μ : EnvironmentVariance.FiniteLaw Ω) (φ : Ω → Bool → Bool)
    (hφ : ∀ ω, Monotone (φ ω)) :
    μ.expect (fun ω => squareJumpResponse (φ ω)) =
      μ.expect (fun ω => oneTimeDifference (φ ω)) / 2 := by
  simp_rw [squareJumpResponse_eq_half _ (hφ _), div_eq_mul_inv]
  exact μ.expect_mul_const _ _

theorem expected_squareJumpResponse_eq_half_difference {Ω : Type*} [Fintype Ω]
    (μ : EnvironmentVariance.FiniteLaw Ω) (φ : Ω → Bool → Bool)
    (hφ : ∀ ω, Monotone (φ ω)) :
    μ.expect (fun ω => squareJumpResponse (φ ω)) =
      (μ.expect (fun ω => if φ ω true then 1 else 0) -
        μ.expect (fun ω => if φ ω false then 1 else 0)) / 2 := by
  rw [expected_squareJumpResponse_eq_half μ φ hφ]
  unfold oneTimeDifference
  rw [μ.expect_sub]

/-- The signed error when a microscopic kernel is compared with a square. -/
def squareError (K S H D : ℝ) : ℝ := K * D - H * S

/-- The common square kernel cancels exactly; the two microscopic rules
need neither the same amplitude nor a limiting amplitude ratio. -/
theorem elimination_identity (K₁ K₂ S₁ S₂ H D : ℝ) :
    D * (K₁ * S₂ - K₂ * S₁) =
      S₂ * squareError K₁ S₁ H D - S₁ * squareError K₂ S₂ H D := by
  unfold squareError
  ring

theorem scaled_abs_bound {K₁ K₂ S₁ S₂ H D a b c C : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hD : c * b ≤ D) (hS₁ : |S₁| ≤ C * a) (hS₂ : |S₂| ≤ C * a) :
    c * b * |K₁ * S₂ - K₂ * S₁| ≤
      C * a * (|squareError K₁ S₁ H D| + |squareError K₂ S₂ H D|) := by
  have hDpos : 0 < D := (mul_pos hc hb).trans_le hD
  calc
    c * b * |K₁ * S₂ - K₂ * S₁| ≤ D * |K₁ * S₂ - K₂ * S₁| :=
      mul_le_mul_of_nonneg_right hD (abs_nonneg _)
    _ = |D * (K₁ * S₂ - K₂ * S₁)| := by rw [abs_mul, abs_of_pos hDpos]
    _ = |S₂ * squareError K₁ S₁ H D - S₁ * squareError K₂ S₂ H D| :=
      congrArg abs (elimination_identity _ _ _ _ _ _)
    _ ≤ |S₂ * squareError K₁ S₁ H D| + |S₁ * squareError K₂ S₂ H D| :=
      abs_sub _ _
    _ = |S₂| * |squareError K₁ S₁ H D| + |S₁| * |squareError K₂ S₂ H D| := by
      rw [abs_mul, abs_mul]
    _ ≤ C * a * |squareError K₁ S₁ H D| + C * a * |squareError K₂ S₂ H D| :=
      add_le_add (mul_le_mul_of_nonneg_right hS₂ (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hS₁ (abs_nonneg _))
    _ = _ := by ring

/-- The precise powers used in direct relative sewing: each pair/square
error is normalized by `a^k * b`, and the eliminated error by `a^(k+1)`.
No lower bound on either microscopic amplitude is needed. -/
theorem normalized_abs_bound (k : ℕ) {K₁ K₂ S₁ S₂ H D a b c C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hD : c * b ≤ D) (hS₁ : |S₁| ≤ C * a) (hS₂ : |S₂| ≤ C * a) :
    |K₁ * S₂ - K₂ * S₁| / a ^ (k + 1) ≤
      (C / c) * ((|squareError K₁ S₁ H D| + |squareError K₂ S₂ H D|) /
        (a ^ k * b)) := by
  have hraw := scaled_abs_bound (K₁ := K₁) (K₂ := K₂) (H := H) hb hc hD hS₁ hS₂
  have hdiv : |K₁ * S₂ - K₂ * S₁| ≤
      (C * a * (|squareError K₁ S₁ H D| + |squareError K₂ S₂ H D|)) / (c * b) := by
    apply (le_div_iff₀ (mul_pos hc hb)).mpr
    simpa only [mul_comm] using hraw
  calc
    |K₁ * S₂ - K₂ * S₁| / a ^ (k + 1) ≤
        ((C * a * (|squareError K₁ S₁ H D| + |squareError K₂ S₂ H D|)) /
          (c * b)) / a ^ (k + 1) :=
      div_le_div_of_nonneg_right hdiv (pow_pos ha _).le
    _ = _ := by
      rw [pow_succ]
      field_simp

/-- A scalar envelope with vanishing iterated limsup gives a uniform small
bound on a family which does not depend on the outer parameter. The explicit
boundedness hypothesis prevents using a default real supremum of an unbounded
set. The mesh threshold may depend on the chosen outer parameter. -/
theorem uniform_small_of_iterated_limsup
    {Mesh Square Location : Type*} (l : Filter Mesh) (m : Filter Square) [m.NeBot]
    (f : Mesh → Location → ℝ) (g : Square → Mesh → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x, |f e x| ≤ C * g h e)
    (hbounded : ∀ᶠ h in m, IsBoundedUnder (· ≤ ·) l (g h))
    (hlim : Tendsto (fun h => limsup (g h) l) m (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ e in l, ∀ x, |f e x| < ε := by
  intro ε hε
  let δ := ε / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (C + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hsmall : ∀ᶠ h in m, limsup (g h) l < δ := hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨h, hb, hbd, hs⟩ := (hbound.and (hbounded.and hsmall)).exists
  have he : ∀ᶠ e in l, g h e < δ := eventually_lt_of_limsup_lt hs hbd
  filter_upwards [hb, he] with e hbe hee
  intro x
  have hmul := mul_le_mul_of_nonneg_left hee.le hC
  have hfx := hbe x
  nlinarith

theorem tendsto_zero_of_iterated_limsup
    {Mesh Square Location : Type*} (l : Filter Mesh) (m : Filter Square) [m.NeBot]
    (f : Mesh → Location → ℝ) (g : Square → Mesh → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x, |f e x| ≤ C * g h e)
    (hbounded : ∀ᶠ h in m, IsBoundedUnder (· ≤ ·) l (g h))
    (hlim : Tendsto (fun h => limsup (g h) l) m (𝓝 0)) (x : Location) :
    Tendsto (fun e => f e x) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [uniform_small_of_iterated_limsup l m f g hC hbound hbounded hlim ε hε]
    with e he
  simpa only [Real.dist_eq, sub_zero] using he x

/-- Two separately vanishing fixed-square limsup envelopes suffice. Their
good sets of square parameters are intersected before a single fixed square
is chosen; neither parameter depends on the mesh. -/
theorem uniform_small_of_two_iterated_limsup
    {Mesh Square Location : Type*} (l : Filter Mesh) (m : Filter Square) [m.NeBot]
    (f : Mesh → Location → ℝ) (g₁ g₂ : Square → Mesh → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x, |f e x| ≤ C * (g₁ h e + g₂ h e))
    (hbounded₁ : ∀ᶠ h in m, IsBoundedUnder (· ≤ ·) l (g₁ h))
    (hbounded₂ : ∀ᶠ h in m, IsBoundedUnder (· ≤ ·) l (g₂ h))
    (hlim₁ : Tendsto (fun h => limsup (g₁ h) l) m (𝓝 0))
    (hlim₂ : Tendsto (fun h => limsup (g₂ h) l) m (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ e in l, ∀ x, |f e x| < ε := by
  intro ε hε
  let δ := ε / (2 * (C + 1))
  have hden : 0 < 2 * (C + 1) := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (2 * (C + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  have hsmall₁ : ∀ᶠ h in m, limsup (g₁ h) l < δ := hlim₁.eventually (gt_mem_nhds hδ)
  have hsmall₂ : ∀ᶠ h in m, limsup (g₂ h) l < δ := hlim₂.eventually (gt_mem_nhds hδ)
  obtain ⟨h, hb, hb₁, hb₂, hs₁, hs₂⟩ :=
    (hbound.and (hbounded₁.and (hbounded₂.and (hsmall₁.and hsmall₂)))).exists
  have he₁ : ∀ᶠ e in l, g₁ h e < δ := eventually_lt_of_limsup_lt hs₁ hb₁
  have he₂ : ∀ᶠ e in l, g₂ h e < δ := eventually_lt_of_limsup_lt hs₂ hb₂
  filter_upwards [hb, he₁, he₂] with e hbe he₁e he₂e
  intro x
  have hmul := mul_le_mul_of_nonneg_left (add_le_add he₁e.le he₂e.le) hC
  have hfx := hbe x
  nlinarith

/-- Uniform direct relative sewing follows from two errors with a common
square kernel. All bounds and all asymptotic inputs remain explicit. In an
application `l` is the mesh limit and `m` is the square-radius limit, both
through positive values. `g` can be a uniform upper envelope over a compact
set of separated anchor locations. It need not be defined by a supremum. -/
theorem direct_relative_sewing_of_common_square
    {Mesh Square Location : Type*} (l : Filter Mesh) (m : Filter Square) [m.NeBot]
    (k : ℕ) (a : Mesh → ℝ) (b : Square → Mesh → ℝ)
    (K₁ K₂ S₁ S₂ : Mesh → Location → ℝ)
    (H D : Square → Mesh → Location → ℝ) (g : Square → Mesh → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hdata : ∀ᶠ h in m, ∀ᶠ e in l, 0 < a e ∧ 0 < b h e ∧
      ∀ x, c * b h e ≤ D h e x ∧ |S₁ e x| ≤ C * a e ∧ |S₂ e x| ≤ C * a e)
    (herror : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      (|squareError (K₁ e x) (S₁ e x) (H h e x) (D h e x)| +
        |squareError (K₂ e x) (S₂ e x) (H h e x) (D h e x)|) /
          ((a e) ^ k * b h e) ≤ g h e)
    (hbounded : ∀ᶠ h in m, IsBoundedUnder (· ≤ ·) l (g h))
    (hlim : Tendsto (fun h => limsup (g h) l) m (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ e in l, ∀ x,
      |K₁ e x * S₂ e x - K₂ e x * S₁ e x| / (a e) ^ (k + 1) < ε := by
  have hbound : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      |(K₁ e x * S₂ e x - K₂ e x * S₁ e x) / (a e) ^ (k + 1)| ≤
        (C / c) * g h e := by
    filter_upwards [hdata, herror] with h hd he
    filter_upwards [hd, he] with e hd he
    intro x
    rw [abs_div, abs_of_pos (pow_pos hd.1 _)]
    exact (normalized_abs_bound k hd.1 hd.2.1 hc (hd.2.2 x).1
      (hd.2.2 x).2.1 (hd.2.2 x).2.2).trans
        (mul_le_mul_of_nonneg_left (he x) (div_nonneg hC hc.le))
  intro ε hε
  have hsmall := uniform_small_of_iterated_limsup l m
    (fun e x => (K₁ e x * S₂ e x - K₂ e x * S₁ e x) / (a e) ^ (k + 1))
    g (div_nonneg hC hc.le) hbound hbounded hlim ε hε
  obtain ⟨h, hd⟩ := hdata.exists
  filter_upwards [hsmall, hd] with e he hd
  intro x
  simpa only [abs_div, abs_of_pos (pow_pos hd.1 _)] using he x

/-- The version matching two separate pair/square estimates. The common `H`
and `D` are the same functions in both errors; changing them with the rule
would invalidate the cancellation and is not permitted by this statement. -/
theorem direct_relative_sewing_of_separate_common_square
    {Mesh Square Location : Type*} (l : Filter Mesh) (m : Filter Square) [m.NeBot]
    (k : ℕ) (a : Mesh → ℝ) (b : Square → Mesh → ℝ)
    (K₁ K₂ S₁ S₂ : Mesh → Location → ℝ)
    (H D : Square → Mesh → Location → ℝ) (g₁ g₂ : Square → Mesh → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hdata : ∀ᶠ h in m, ∀ᶠ e in l, 0 < a e ∧ 0 < b h e ∧
      ∀ x, c * b h e ≤ D h e x ∧ |S₁ e x| ≤ C * a e ∧ |S₂ e x| ≤ C * a e)
    (herror₁ : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      |squareError (K₁ e x) (S₁ e x) (H h e x) (D h e x)| /
        ((a e) ^ k * b h e) ≤ g₁ h e)
    (herror₂ : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      |squareError (K₂ e x) (S₂ e x) (H h e x) (D h e x)| /
        ((a e) ^ k * b h e) ≤ g₂ h e)
    (hbounded₁ : ∀ᶠ h in m, IsBoundedUnder (· ≤ ·) l (g₁ h))
    (hbounded₂ : ∀ᶠ h in m, IsBoundedUnder (· ≤ ·) l (g₂ h))
    (hlim₁ : Tendsto (fun h => limsup (g₁ h) l) m (𝓝 0))
    (hlim₂ : Tendsto (fun h => limsup (g₂ h) l) m (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ e in l, ∀ x,
      |K₁ e x * S₂ e x - K₂ e x * S₁ e x| / (a e) ^ (k + 1) < ε := by
  have hbound : ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      |(K₁ e x * S₂ e x - K₂ e x * S₁ e x) / (a e) ^ (k + 1)| ≤
        (C / c) * (g₁ h e + g₂ h e) := by
    filter_upwards [hdata, herror₁, herror₂] with h hd he₁ he₂
    filter_upwards [hd, he₁, he₂] with e hd he₁ he₂
    intro x
    rw [abs_div, abs_of_pos (pow_pos hd.1 _)]
    apply (normalized_abs_bound k (H := H h e x) hd.1 hd.2.1 hc (hd.2.2 x).1
      (hd.2.2 x).2.1 (hd.2.2 x).2.2).trans
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hC hc.le)
    rw [add_div]
    exact add_le_add (he₁ x) (he₂ x)
  intro ε hε
  have hsmall := uniform_small_of_two_iterated_limsup l m
    (fun e x => (K₁ e x * S₂ e x - K₂ e x * S₁ e x) / (a e) ^ (k + 1))
    g₁ g₂ (div_nonneg hC hc.le) hbound hbounded₁ hbounded₂ hlim₁ hlim₂ ε hε
  obtain ⟨h, hd⟩ := hdata.exists
  filter_upwards [hsmall, hd] with e he hd
  intro x
  simpa only [abs_div, abs_of_pos (pow_pos hd.1 _)] using he x

#print axioms squareJumpResponse_eq_half
#print axioms square_pushforward
#print axioms expected_squareJumpResponse_eq_half
#print axioms elimination_identity
#print axioms normalized_abs_bound
#print axioms uniform_small_of_iterated_limsup
#print axioms direct_relative_sewing_of_common_square
#print axioms direct_relative_sewing_of_separate_common_square

end ExceptionalTimes.CommonSquare
