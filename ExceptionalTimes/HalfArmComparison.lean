import ExceptionalTimes.HalfPlaneArms
import ExceptionalTimes.ArmEnlargement

/-! The static half-plane exponent is stronger than the four-arm lower
power. This module applies that comparison to the literal finite fair-site
three-arm event; its microscopic cutoff is never removed. -/

open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

theorem power_two_le_four_cost {r R g c C α : ℝ}
    (hr : 0<r) (hrR : r≤R) (hg : g≤2) (hc : 0<c) (hC : 0≤C)
    (hlower : c*(r/R)^g ≤ α) : C*(r/R)^2 ≤ (C/c)*α := by
  have hR := hr.trans_le hrR
  have hp : (r/R)^2 ≤ (r/R)^g := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_ge (div_pos hr hR) ((div_le_one hR).mpr hrR) hg)
  have hq : (r/R)^g ≤ α/c := (le_div_iff₀ hc).mpr (by nlinarith)
  calc
    C*(r/R)^2 ≤ C*(r/R)^g := mul_le_mul_of_nonneg_left hp hC
    _ ≤ C*(α/c) := mul_le_mul_of_nonneg_left hq hC
    _ = (C/c)*α := by ring

/-- A one-probe static application, on its genuine normalized finite law.
`hlower` is precisely the published lower four-arm power at these radii. -/
theorem halfThree_probability_le_four
    {B₀ C c g : ℝ} (hsource : PublishedHalfThreeArmBound B₀ C)
    (P : HalfProbe) (D : Finset Site) (hmesh : B₀*P.mesh ≤ P.innerRadius)
    (hD : P.region ⊆ (D : Set Site)) (hg : g≤2) (hc : 0<c) (hC : 0≤C)
    (α : ℝ → ℝ → ℝ)
    (hlower : c*(P.innerRadius/P.outerRadius)^g ≤ α P.innerRadius P.outerRadius) :
    EnvironmentVariance.probability (ProbeProduct.fairSites D)
      (fun ω => HalfThreeArms P (completeColors D ω)) ≤
      (C/c)*α P.innerRadius P.outerRadius := by
  apply (hsource P D hmesh hD).trans
  exact power_two_le_four_cost P.inner_pos (by linarith [P.radii,P.inner_pos]) hg hc hC hlower

/-- Quasi-multiplicativity converts the same actual half-plane event to
the single-scale profile used by the forest telescope. -/
theorem halfThree_probability_le_profile
    {B₀ C c g Q : ℝ} (hsource : PublishedHalfThreeArmBound B₀ C)
    (P : HalfProbe) (D : Finset Site) (hmesh : B₀*P.mesh ≤ P.innerRadius)
    (hD : P.region ⊆ (D : Set Site)) (hg : g≤2) (hc : 0<c) (hC : 0≤C)
    (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hlower : c*(P.innerRadius/P.outerRadius)^g ≤ α P.innerRadius P.outerRadius)
    (hquasi : α P.innerRadius P.outerRadius ≤ Q*(p P.innerRadius/p P.outerRadius)) :
    EnvironmentVariance.probability (ProbeProduct.fairSites D)
      (fun ω => HalfThreeArms P (completeColors D ω)) ≤
      (C*Q/c)*(p P.innerRadius/p P.outerRadius) := by
  apply (halfThree_probability_le_four hsource P D hmesh hD hg hc hC α hlower).trans
  have h := mul_le_mul_of_nonneg_left hquasi (div_nonneg hC hc.le)
  convert h using 1
  ring

/-- Two separated arm pieces lose only the lower-power cost of their
intervening scale gap. This is an algebraic consequence of the stated
single-scale profile inequality, not a mixed-event probability premise. -/
theorem profile_bridge_gap (p : ℝ → ℝ) {a b c d C g : ℝ}
    (hpa : 0≤p a) (hpb : 0<p b) (hpd : 0<p d)
    (hgap : p c ≤ C*(c/b)^g*p b) :
    (p a/p b)*(p c/p d) ≤ C*(c/b)^g*(p a/p d) := by
  have h := mul_le_mul_of_nonneg_left hgap (div_nonneg hpa hpb.le)
  have hh := div_le_div_of_nonneg_right h hpd.le
  convert hh using 1 <;> field_simp

#print axioms halfThree_probability_le_four
#print axioms halfThree_probability_le_profile
#print axioms profile_bridge_gap

end ExceptionalTimes.PairSquareSewing

