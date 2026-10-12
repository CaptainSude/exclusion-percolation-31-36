import ExceptionalTimes.Annulus

/-!
Concrete finite annular one-arm events and their cylinder measurability.
The event uses an actual monochromatic simple triangular-lattice path
contained in the closed hexagonal annulus. No RSW, arm exponent, gluing,
or correlation estimate is assumed or asserted in this file.
-/

namespace ExceptionalTimes

set_option autoImplicit false
open Annulus

theorem closedAnnulus_subset_box (r R : ℕ) :
    closedAnnulus r R ⊆ (latticeBox R : Set Site) := by
  intro v hv
  have hR : max (max |v.1| |v.2|) |v.1 + v.2| ≤ (R : ℤ) := hv.2
  have hx := (le_max_left |v.1| |v.2|).trans ((le_max_left _ _).trans hR)
  have hy := (le_max_right |v.1| |v.2|).trans ((le_max_left _ _).trans hR)
  change v ∈ latticeBox R
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  exact ⟨abs_le.mp hx, abs_le.mp hy⟩

theorem finite_closedAnnulus (r R : ℕ) : (closedAnnulus r R).Finite :=
  (latticeBox R).finite_toSet.subset (closedAnnulus_subset_box r R)

/-- An actual simple monochromatic connection between the two boundaries. -/
def RadialArm (color : Bool) (ω : Configuration) (r R : ℕ) : Prop :=
  ∃ x ∈ hexBoundary r, ∃ y ∈ hexBoundary R, ∃ p : triangularGraph.Walk x y,
    p.IsPath ∧ ∀ z ∈ p.support, z ∈ closedAnnulus r R ∧ ω z = color

theorem radialArm_congr_of_eqOn (color : Bool) {ω η : Configuration} {r R : ℕ}
    (h : Set.EqOn ω η (closedAnnulus r R)) :
    RadialArm color ω r R ↔ RadialArm color η r R := by
  constructor
  · rintro ⟨x, hx, y, hy, p, hp, hsupport⟩
    refine ⟨x, hx, y, hy, p, hp, ?_⟩
    intro z hz
    obtain ⟨hregion, hcolor⟩ := hsupport z hz
    exact ⟨hregion, (h hregion).symm.trans hcolor⟩
  · rintro ⟨x, hx, y, hy, p, hp, hsupport⟩
    refine ⟨x, hx, y, hy, p, hp, ?_⟩
    intro z hz
    obtain ⟨hregion, hcolor⟩ := hsupport z hz
    exact ⟨hregion, (h hregion).trans hcolor⟩

theorem radialArm_black_mono {ω η : Configuration} {r R : ℕ}
    (h : ω ≤ η) (hω : RadialArm true ω r R) : RadialArm true η r R := by
  obtain ⟨x, hx, y, hy, p, hp, hsupport⟩ := hω
  refine ⟨x, hx, y, hy, p, hp, ?_⟩
  intro z hz
  obtain ⟨hregion, hcolor⟩ := hsupport z hz
  refine ⟨hregion, ?_⟩
  have hz' := h z
  rw [hcolor] at hz'
  exact le_antisymm le_top hz'

theorem radialArm_white_antitone {ω η : Configuration} {r R : ℕ}
    (h : ω ≤ η) (hη : RadialArm false η r R) : RadialArm false ω r R := by
  obtain ⟨x, hx, y, hy, p, hp, hsupport⟩ := hη
  refine ⟨x, hx, y, hy, p, hp, ?_⟩
  intro z hz
  obtain ⟨hregion, hcolor⟩ := hsupport z hz
  refine ⟨hregion, ?_⟩
  have hz' := h z
  rw [hcolor] at hz'
  exact le_antisymm hz' bot_le

theorem measurableSet_of_finite_color_support (S : Finset Site)
    (E : Configuration → Prop)
    (hlocal : ∀ ω η, Set.EqOn ω η (S : Set Site) → (E ω ↔ E η)) :
    MeasurableSet {ω | E ω} := by
  classical
  let restrict : Configuration → (↥S → Bool) := fun ω v => ω v
  let complete : (↥S → Bool) → Configuration := fun ξ v =>
    if hv : v ∈ S then ξ ⟨v, hv⟩ else false
  have hrestrict : Measurable restrict :=
    measurable_pi_iff.mpr fun v => measurable_pi_apply (v : Site)
  have hfinite : MeasurableSet {ξ : ↥S → Bool | E (complete ξ)} :=
    (Set.toFinite _).measurableSet
  have hevent : {ω | E ω} = restrict ⁻¹' {ξ | E (complete ξ)} := by
    ext ω
    apply hlocal
    intro v hv
    have hv' : v ∈ S := hv
    simp [complete, restrict, hv']
  rw [hevent]
  exact hfinite.preimage hrestrict

theorem measurableSet_radialArm (color : Bool) (r R : ℕ) :
    MeasurableSet {ω | RadialArm color ω r R} := by
  apply measurableSet_of_finite_color_support (latticeBox R)
  intro ω η h
  exact radialArm_congr_of_eqOn color (h.mono (closedAnnulus_subset_box r R))

/-- Boundary trimming does not change the event: an arm may be chosen
to touch each annular boundary only at its own endpoint. -/
theorem radialArm_iff_proper (color : Bool) (ω : Configuration) (r R : ℕ) :
    RadialArm color ω r R ↔
      ∃ x ∈ hexBoundary r, ∃ y ∈ hexBoundary R, ∃ p : triangularGraph.Walk x y,
        p.IsPath ∧
        (∀ z ∈ p.support, z ∈ closedAnnulus r R ∧ ω z = color) ∧
        (∀ z ∈ p.support, z ∈ hexBoundary r → z = x) ∧
        (∀ z ∈ p.support, z ∈ hexBoundary R → z = y) := by
  constructor
  · rintro ⟨u, hu, v, hv, p, hp, hsupport⟩
    obtain ⟨x, hx, y, hy, q, hq, hsub, hinner, houter⟩ :=
      trim_path_between_sets (hexBoundary r) (hexBoundary R) p hp hu hv
    exact ⟨x, hx, y, hy, q, hq,
      fun z hz => hsupport z (hsub.support_subset hz), hinner, houter⟩
  · rintro ⟨x, hx, y, hy, p, hp, hsupport, _, _⟩
    exact ⟨x, hx, y, hy, p, hp, hsupport⟩

end ExceptionalTimes

#print axioms ExceptionalTimes.finite_closedAnnulus
#print axioms ExceptionalTimes.radialArm_black_mono
#print axioms ExceptionalTimes.measurableSet_radialArm
#print axioms ExceptionalTimes.radialArm_iff_proper
