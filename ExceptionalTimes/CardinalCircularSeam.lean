import ExceptionalTimes.CardinalGuardedSeam

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open Annulus AnnularCollars

/-- The exact sites on the inside of a Euclidean circular seam. The
boundary belongs to the inside, a deterministic convention. -/
noncomputable def circularSeamSites (Λ : Finset Site) (mesh radius : ℝ) : Finset Site :=
  Λ.filter (fun z => mesh*‖triangularEmbedding z‖ ≤ radius)

theorem circularSeamSites_physical {Λ : Finset Site} (mesh radius : ℝ) (hm : 0 ≤ mesh)
    (z : Site) : z ∈ circularSeamSites Λ mesh radius ↔
      z ∈ Λ ∧ ‖position mesh z‖ ≤ radius := by
  simp only [circularSeamSites,Finset.mem_filter,position,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]

theorem cardinalEndpoint_box_hex_bounds (t : ℤ) (w : ℕ) (hwidth : 4*w < t)
    (i : Fin 4) {z : Site} (hz : z-cardinalEndpoint t i ∈ latticeBox (2*w)) :
    t-2*w ≤ hexRadius z ∧ hexRadius z ≤ t+4*w := by
  have hdom := cardinalEndpoint_box_subset t t w le_rfl i t (Or.inl rfl) hz
  have h := cardinalTrack_hex_bounds (t-2*w) (t+2*w) (2*w) (by omega) (by omega) i hdom
  constructor <;> omega

theorem cardinal_inner_guard_in_circle {Λ : Finset Site} (r R : ℤ) (w : ℕ)
    (hwidth : 4*w < r) (hrR : r ≤ R)
    (hΛ : cardinalSupport (r-2*w) (R+2*w) (2*w) ⊆ Λ)
    (mesh radius : ℝ) (hm : 0 < mesh)
    (hinner : 2*mesh*(r+4*w) ≤ radius) (i : Fin 4)
    (C : SurroundingCircuit w (2*w)) {z : Site}
    (hz : z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support) :
    z ∈ circularSeamSites Λ mesh radius := by
  have hb := shiftedCircuit_inside _ C hz
  have hd := cardinalEndpoint_box_subset r R w hrR i r (Or.inl rfl) hb
  have hfit := cardinalConnector_fits (r-2*w) (R+2*w) (2*w) (by omega) hΛ (i,false,false)
  apply Finset.mem_filter.mpr
  refine ⟨hfit.1 hd,?_⟩
  have hh := (cardinalEndpoint_box_hex_bounds r w hwidth i hb).2
  have hh' : (hexRadius z : ℝ) ≤ r+4*w := by exact_mod_cast hh
  have hn := (hexRadius_norm_comparison z).2
  nlinarith

theorem cardinal_outer_guard_out_circle {Λ : Finset Site} (R : ℤ) (w : ℕ)
    (hwidth : 4*w < R) (mesh radius : ℝ) (hm : 0 < mesh)
    (houter : 4*radius < mesh*(R-2*w)) (i : Fin 4)
    (D : SurroundingCircuit w (2*w)) {z : Site}
    (hz : z ∈ (shiftedCircuit (cardinalEndpoint R i) D).support) :
    z ∉ circularSeamSites Λ mesh radius := by
  intro hzIn
  have hradius := (Finset.mem_filter.mp hzIn).2
  have hh := (cardinalEndpoint_box_hex_bounds R w hwidth i (shiftedCircuit_inside _ D hz)).1
  have hh' : (R:ℝ)-2*w ≤ hexRadius z := by exact_mod_cast hh
  have hn := (hexRadius_norm_comparison z).1
  nlinarith

/-- Literal circular-seam version of the shared-guard connector
construction. All circle containments follow from the displayed numeric
margins; no square/circle dictionary is assumed. -/
theorem cardinal_circular_guard_connections {Λ : Finset Site} (r R : ℤ) (w : ℕ)
    (hwidth : 4*w < r) (hgap : 3*w < R-r)
    (hΛ : cardinalSupport (r-2*w) (R+2*w) (2*w) ⊆ Λ)
    (mesh radius : ℝ) (hm : 0 < mesh)
    (hinner : 2*mesh*(r+4*w) ≤ radius) (houter : 4*radius < mesh*(R-2*w))
    (ω : Sources Λ) (C D : Bool → Fin 4 → SurroundingCircuit w (2*w))
    (hC : ∀ a i z, z ∈ (shiftedCircuit (cardinalEndpoint r i) (C a i)).support →
      complete (if a then ω.2 else ω.1) z=decide (i.val % 2=0))
    (hD : ∀ b i z, z ∈ (shiftedCircuit (cardinalEndpoint R i) (D b i)).support →
      complete (if b then ω.2 else ω.1) z=decide (i.val % 2=0))
    (hcross : ∀ j : Fin 4 × Bool × Bool,
      (cardinalConnector r R w j).event (circularSeamSites Λ mesh radius) ω)
    (x y : Bool → Fin 4 → Site)
    (hx : ∀ a i, x a i ∈ (shiftedCircuit (cardinalEndpoint r i) (C a i)).support)
    (hy : ∀ b i, y b i ∈ (shiftedCircuit (cardinalEndpoint R i) (D b i)).support) :
    ∀ a b, ∃ p : ∀ i, triangularGraph.Walk (x a i) (y b i),
      (∀ i, (p i).IsPath) ∧
      (∀ i z, z ∈ (p i).support →
        z ∈ (cardinalTrack (r-2*w) (R+2*w) (2*w) i).domain ∧
          complete (sewnField (circularSeamSites Λ mesh radius) ω a b) z=decide (i.val % 2=0)) ∧
      (∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support) := by
  intro a b
  apply cardinal_four_guarded_joins r R w hgap hwidth
    (complete (sewnField (circularSeamSites Λ mesh radius) ω a b)) (C a) (D b)
  · intro i z hz
    rw [complete_sewnField_inside _ _ _ _
      (cardinal_inner_guard_in_circle r R w hwidth (by omega) hΛ mesh radius hm hinner i (C a i) hz)]
    exact hC a i z hz
  · intro i z hz
    rw [complete_sewnField_outside _ _ _ _
      (cardinal_outer_guard_out_circle R w (by omega) mesh radius hm houter i (D b i) hz)]
    exact hD b i z hz
  · intro i
    exact hcross (i,a,b)
  · exact hx a
  · exact hy b

#print axioms circularSeamSites_physical
#print axioms cardinal_circular_guard_connections

end ExceptionalTimes.PairSquareSewing
