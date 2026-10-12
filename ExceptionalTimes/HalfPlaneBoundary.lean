import ExceptionalTimes.HoleFilling
import ExceptionalTimes.TriangularPlane

/-!
# Literal flat-side charts for the inner square

The claims here concern the real lattice boxes and polygonal walk traces.
They check that a probe away from the corners sees precisely a half-plane,
and that white paths in the filled configuration stay on its exterior
side. They do not assert existence or cyclic order of any arm.
-/

namespace ExceptionalTimes.HalfPlaneBoundary

open HoleFilling TriangularPlane

theorem right_probe_box_iff (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox ((r : ℤ), k) n) :
    z ∈ latticeBox r ↔ z.1 ≤ (r : ℤ) := by
  rcases z with ⟨x, y⟩
  simp only [probeBox, Set.mem_ofPred_eq, latticeBox, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc] at hz ⊢
  omega

theorem left_probe_box_iff (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox (-(r : ℤ), k) n) :
    z ∈ latticeBox r ↔ -(r : ℤ) ≤ z.1 := by
  rcases z with ⟨x, y⟩
  simp only [probeBox, Set.mem_ofPred_eq, latticeBox, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc] at hz ⊢
  omega

theorem top_probe_box_iff (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox (k, (r : ℤ)) n) :
    z ∈ latticeBox r ↔ z.2 ≤ (r : ℤ) := by
  rcases z with ⟨x, y⟩
  simp only [probeBox, Set.mem_ofPred_eq, latticeBox, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc] at hz ⊢
  omega

theorem bottom_probe_box_iff (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox (k, -(r : ℤ)) n) :
    z ∈ latticeBox r ↔ -(r : ℤ) ≤ z.2 := by
  rcases z with ⟨x, y⟩
  simp only [probeBox, Set.mem_ofPred_eq, latticeBox, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc] at hz ⊢
  omega

theorem filled_white_outside (ω : Configuration) (r : ℕ) {z : Site}
    (hz : fillBox ω r z = false) : z ∉ latticeBox r := by
  intro hmem
  have hblack := fillBox_inside ω r hmem
  simp only [hz, Bool.false_eq_true] at hblack

theorem filled_white_right_probe (ω : Configuration) (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox ((r : ℤ), k) n)
    (hc : fillBox ω r z = false) : (r : ℤ) < z.1 := by
  have hn := filled_white_outside ω r hc
  rw [right_probe_box_iff r n k hlo hhi hz] at hn
  exact lt_of_not_ge hn

theorem filled_white_left_probe (ω : Configuration) (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox (-(r : ℤ), k) n)
    (hc : fillBox ω r z = false) : z.1 < -(r : ℤ) := by
  have hn := filled_white_outside ω r hc
  rw [left_probe_box_iff r n k hlo hhi hz] at hn
  exact lt_of_not_ge hn

theorem filled_white_top_probe (ω : Configuration) (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox (k, (r : ℤ)) n)
    (hc : fillBox ω r z = false) : (r : ℤ) < z.2 := by
  have hn := filled_white_outside ω r hc
  rw [top_probe_box_iff r n k hlo hhi hz] at hn
  exact lt_of_not_ge hn

theorem filled_white_bottom_probe (ω : Configuration) (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {z : Site} (hz : z ∈ probeBox (k, -(r : ℤ)) n)
    (hc : fillBox ω r z = false) : z.2 < -(r : ℤ) := by
  have hn := filled_white_outside ω r hc
  rw [bottom_probe_box_iff r n k hlo hhi hz] at hn
  exact lt_of_not_ge hn

/-- Convex interpolation cannot carry a lattice edge across a straight
boundary when both endpoints are strictly on the exterior side. -/
theorem edgePoint_right {a b : Site} {r t : ℝ}
    (ha : r < (a.1 : ℝ)) (hb : r < (b.1 : ℝ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : r < (edgePoint a b t).1 := by
  have h₁ : 0 ≤ (1 - t) * ((a.1 : ℝ) - r) := mul_nonneg (by linarith) (by linarith)
  have h₂ : 0 ≤ t * ((b.1 : ℝ) - r) := mul_nonneg ht0 (by linarith)
  by_cases ht : t = 0
  · simpa [edgePoint, ht] using ha
  · have h₂' : 0 < t * ((b.1 : ℝ) - r) :=
      mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) (by linarith)
    simp only [edgePoint]
    nlinarith

/-- Every point of the literal polygonal trace stays in the open
half-plane when all its lattice vertices do. -/
theorem walkTrace_right {u v : Site} (p : triangularGraph.Walk u v) (r : ℝ)
    (hp : ∀ a ∈ p.support, r < (a.1 : ℝ)) :
    ∀ z ∈ walkTrace p, r < z.1 := by
  intro z hz
  rcases walkTrace_point_or_edge p hz with ⟨a, ha, rfl⟩ |
      ⟨a, ha, b, hb, _, t, ht0, ht1, rfl⟩
  · exact hp a ha
  · exact edgePoint_right (hp a ha) (hp b hb) ht0 ht1

/-- The original inner-side geometry has no hidden edge excursions into
the filled hole: an entire white walk retained in this flat-side probe
has its whole polygonal trace in the exterior open half-plane. -/
theorem filled_white_walk_right (ω : Configuration) (r n : ℕ) (k : ℤ)
    (hlo : -(r : ℤ) + n ≤ k) (hhi : k ≤ (r : ℤ) - n)
    {u v : Site} (p : triangularGraph.Walk u v)
    (hprobe : ∀ a ∈ p.support, a ∈ probeBox ((r : ℤ), k) n)
    (hwhite : ∀ a ∈ p.support, fillBox ω r a = false) :
    ∀ z ∈ walkTrace p, (r : ℝ) < z.1 := by
  apply walkTrace_right
  intro a ha
  exact_mod_cast filled_white_right_probe ω r n k hlo hhi (hprobe a ha) (hwhite a ha)

#print axioms right_probe_box_iff
#print axioms left_probe_box_iff
#print axioms top_probe_box_iff
#print axioms bottom_probe_box_iff
#print axioms filled_white_walk_right

end ExceptionalTimes.HalfPlaneBoundary
