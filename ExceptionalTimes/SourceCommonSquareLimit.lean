import ExceptionalTimes.CommonSquare

/-! Direct epsilon/eventually elimination of a common fixed square.
The microscopic expressions do not depend on the square parameter. A
single square is chosen only after the tolerance, before the mesh limit.
All calibration upper and lower bounds remain explicit premises. -/

open Filter
open scoped Topology
namespace ExceptionalTimes.CommonSquare

theorem direct_relative_sewing_of_eventual_square_error
    {Mesh Square Location : Type*} (l : Filter Mesh) (m : Filter Square) [m.NeBot]
    (k : ℕ) (a : Mesh → ℝ) (b : Square → Mesh → ℝ)
    (K₁ K₂ S₁ S₂ : Mesh → Location → ℝ)
    (H D : Square → Mesh → Location → ℝ)
    {c C : ℝ} (hc : 0<c) (hC : 0≤C)
    (hdata : ∀ᶠ h in m, ∀ᶠ e in l, 0<a e ∧ 0<b h e ∧
      ∀ x, c*b h e≤D h e x ∧ |S₁ e x|≤C*a e ∧ |S₂ e x|≤C*a e)
    (herror : ∀ δ : ℝ, 0<δ → ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      (|squareError (K₁ e x) (S₁ e x) (H h e x) (D h e x)| +
        |squareError (K₂ e x) (S₂ e x) (H h e x) (D h e x)|) /
          ((a e)^k*b h e) ≤ δ) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ e in l, ∀ x,
      |K₁ e x*S₂ e x-K₂ e x*S₁ e x|/(a e)^(k+1)<ε := by
  intro ε hε
  let r := C/c
  have hr : 0≤r := div_nonneg hC hc.le
  let δ := ε/(r+1)
  have hden : 0<r+1 := by linarith
  have hδ : 0<δ := div_pos hε hden
  have hδeq : δ*(r+1)=ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨h,hd,he⟩ := (hdata.and (herror δ hδ)).exists
  filter_upwards [hd,he] with e hd he
  intro x
  have hb := (normalized_abs_bound k hd.1 hd.2.1 hc (hd.2.2 x).1
    (hd.2.2 x).2.1 (hd.2.2 x).2.2).trans
      (mul_le_mul_of_nonneg_left (he x) hr)
  change _≤r*δ at hb
  nlinarith

/-- Separate estimates can use the same square parameter. Their good
square sets are intersected before the fixed square is chosen. -/
theorem direct_relative_sewing_of_separate_eventual_square_errors
    {Mesh Square Location : Type*} (l : Filter Mesh) (m : Filter Square) [m.NeBot]
    (k : ℕ) (a : Mesh → ℝ) (b : Square → Mesh → ℝ)
    (K₁ K₂ S₁ S₂ : Mesh → Location → ℝ)
    (H D : Square → Mesh → Location → ℝ)
    {c C : ℝ} (hc : 0<c) (hC : 0≤C)
    (hdata : ∀ᶠ h in m, ∀ᶠ e in l, 0<a e ∧ 0<b h e ∧
      ∀ x, c*b h e≤D h e x ∧ |S₁ e x|≤C*a e ∧ |S₂ e x|≤C*a e)
    (herror₁ : ∀ δ : ℝ, 0<δ → ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      |squareError (K₁ e x) (S₁ e x) (H h e x) (D h e x)| /
        ((a e)^k*b h e) ≤ δ)
    (herror₂ : ∀ δ : ℝ, 0<δ → ∀ᶠ h in m, ∀ᶠ e in l, ∀ x,
      |squareError (K₂ e x) (S₂ e x) (H h e x) (D h e x)| /
        ((a e)^k*b h e) ≤ δ) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ e in l, ∀ x,
      |K₁ e x*S₂ e x-K₂ e x*S₁ e x|/(a e)^(k+1)<ε := by
  apply direct_relative_sewing_of_eventual_square_error l m k a b K₁ K₂ S₁ S₂ H D hc hC hdata
  intro δ hδ
  filter_upwards [herror₁ (δ/2) (by linarith),herror₂ (δ/2) (by linarith)] with h he₁ he₂
  filter_upwards [he₁,he₂] with e he₁ he₂
  intro x
  rw [add_div]
  have hh := add_le_add (he₁ x) (he₂ x)
  linarith

#print axioms direct_relative_sewing_of_eventual_square_error
#print axioms direct_relative_sewing_of_separate_eventual_square_errors
end ExceptionalTimes.CommonSquare
