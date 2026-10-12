import ExceptionalTimes.CardinalWideProbability
import ExceptionalTimes.CardinalCircularSeam

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open Annulus AnnularCollars EnvironmentVariance

theorem cardinalEndpoint_wide_hex_bounds (t : ℤ) (U : ℕ) (hwidth : 2*U < t)
    (i : Fin 4) {z : Site} (hz : z-cardinalEndpoint t i ∈ latticeBox U) :
    t-U ≤ hexRadius z ∧ hexRadius z ≤ t+2*U := by
  have hdom := cardinalEndpoint_wide_box_subset t t U le_rfl i t (Or.inl rfl) hz
  have h := cardinalTrack_hex_bounds (t-U) (t+U) U (by omega) (by omega) i hdom
  constructor <;> omega

theorem wide_inner_guard_in_circle {Λ : Finset Site} (r R : ℤ) (w U : ℕ)
    (hwidth : 2*U < r) (hrR : r ≤ R) (hΛ : cardinalSupport (r-U) (R+U) U ⊆ Λ)
    (mesh radius : ℝ) (hm : 0 < mesh) (hinner : 2*mesh*(r+2*U) ≤ radius)
    (i : Fin 4) (C : SurroundingCircuit w U) {z : Site}
    (hz : z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support) :
    z ∈ circularSeamSites Λ mesh radius := by
  have hb := shiftedCircuit_inside _ C hz
  have hd := cardinalEndpoint_wide_box_subset r R U hrR i r (Or.inl rfl) hb
  have hfit := cardinalConnector_fits (r-U) (R+U) U (by omega) hΛ (i,false,false)
  apply Finset.mem_filter.mpr
  refine ⟨hfit.1 hd,?_⟩
  have hh := (cardinalEndpoint_wide_hex_bounds r U hwidth i hb).2
  have hh' : (hexRadius z : ℝ) ≤ r+2*U := by exact_mod_cast hh
  have hn := (hexRadius_norm_comparison z).2
  nlinarith

theorem wide_outer_guard_out_circle {Λ : Finset Site} (R : ℤ) (w U : ℕ)
    (hwidth : 2*U < R) (mesh radius : ℝ) (hm : 0 < mesh)
    (houter : 4*radius < mesh*(R-U)) (i : Fin 4) (D : SurroundingCircuit w U) {z : Site}
    (hz : z ∈ (shiftedCircuit (cardinalEndpoint R i) D).support) :
    z ∉ circularSeamSites Λ mesh radius := by
  intro hzIn
  have hradius := (Finset.mem_filter.mp hzIn).2
  have hh := (cardinalEndpoint_wide_hex_bounds R U hwidth i (shiftedCircuit_inside _ D hz)).1
  have hh' : (R:ℝ)-U ≤ hexRadius z := by exact_mod_cast hh
  have hn := (hexRadius_norm_comparison z).1
  nlinarith

/-- Concrete common-witness outcome of a circular connector space.
Each source contributes four inner and four outer guards. Every choice of
one site on each guard is joined in every sewn field by disjoint simple
paths of the prescribed alternating colors, inside the actual tracks. -/
def WideCircularConnections {Λ : Finset Site} (r R : ℤ) (w U : ℕ)
    (mesh radius : ℝ) (ω : Sources Λ) : Prop :=
  ∃ C D : Bool → Fin 4 → SurroundingCircuit w U,
    (∀ a i z, z ∈ (shiftedCircuit (cardinalEndpoint r i) (C a i)).support →
      complete (if a then ω.2 else ω.1) z=decide (i.val % 2=0)) ∧
    (∀ b i z, z ∈ (shiftedCircuit (cardinalEndpoint R i) (D b i)).support →
      complete (if b then ω.2 else ω.1) z=decide (i.val % 2=0)) ∧
    ∀ a b (x y : Fin 4 → Site),
      (∀ i, x i ∈ (shiftedCircuit (cardinalEndpoint r i) (C a i)).support) →
      (∀ i, y i ∈ (shiftedCircuit (cardinalEndpoint R i) (D b i)).support) →
      ∃ p : ∀ i, triangularGraph.Walk (x i) (y i),
        (∀ i, (p i).IsPath) ∧
        (∀ i z, z ∈ (p i).support → z ∈ (cardinalTrack (r-U) (R+U) U i).domain ∧
          complete (sewnField (circularSeamSites Λ mesh radius) ω a b) z=decide (i.val % 2=0)) ∧
        (∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support)

theorem wide_requirements_imply_circular_connections {Λ : Finset Site}
    (r R : ℤ) (w U : ℕ) (hwU : w ≤ U) (hwidth : 2*U < r)
    (hgap : (w:ℤ)+U < R-r) (hΛ : cardinalSupport (r-U) (R+U) U ⊆ Λ)
    (mesh radius : ℝ) (hm : 0 < mesh)
    (hinner : 2*mesh*(r+2*U) ≤ radius) (houter : 4*radius < mesh*(R-U))
    (ω : Sources Λ)
    (h : ∀ j, wideCardinalRequirement r R w U (circularSeamSites Λ mesh radius) j ω) :
    WideCircularConnections r R w U mesh radius ω := by
  have hC : ∀ (a : Bool) (i : Fin 4), ∃ C : SurroundingCircuit w U,
      ∀ z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support,
        complete (if a then ω.2 else ω.1) z=decide (i.val % 2=0) := by
    intro a i
    exact h (.inr (false,i,a))
  have hD : ∀ (b : Bool) (i : Fin 4), ∃ D : SurroundingCircuit w U,
      ∀ z ∈ (shiftedCircuit (cardinalEndpoint R i) D).support,
        complete (if b then ω.2 else ω.1) z=decide (i.val % 2=0) := by
    intro b i
    exact h (.inr (true,i,b))
  choose C hC using hC
  choose D hD using hD
  refine ⟨C,D,hC,hD,?_⟩
  intro a b x y hx hy
  let η := complete (sewnField (circularSeamSites Λ mesh radius) ω a b)
  have hCin (i : Fin 4) (z : Site)
      (hz : z ∈ (shiftedCircuit (cardinalEndpoint r i) (C a i)).support) :
      η z=decide (i.val % 2=0) := by
    dsimp only [η]
    rw [complete_sewnField_inside _ _ _ _
      (wide_inner_guard_in_circle r R w U hwidth (by omega) hΛ mesh radius hm hinner i (C a i) hz)]
    exact hC a i z hz
  have hDout (i : Fin 4) (z : Site)
      (hz : z ∈ (shiftedCircuit (cardinalEndpoint R i) (D b i)).support) :
      η z=decide (i.val % 2=0) := by
    dsimp only [η]
    rw [complete_sewnField_outside _ _ _ _
      (wide_outer_guard_out_circle R w U (by omega) mesh radius hm houter i (D b i) hz)]
    exact hD b i z hz
  have hp (i : Fin 4) := cardinal_wide_guarded_join r R w U hwU hgap i
    (decide (i.val % 2=0)) η (C a i) (D b i) (hCin i) (hDout i)
    (h (.inl (i,a,b))) (hx i) (hy i)
  choose p hpPath hpColor using hp
  refine ⟨p,hpPath,hpColor,?_⟩
  intro i j hij
  apply List.disjoint_left.mpr
  intro z hzi hzj
  exact Finset.disjoint_left.mp (cardinal_wide_pairwise r R U hwidth hij)
    (hpColor i z hzi).1 (hpColor j z hzj).1

/-- The finite circular connector construction has a uniform positive
probability derived from the existing published static inputs. This is
the seam-space connector component only: sleeve necklaces, retained
extensions, bad trims and the one-trial comparison are separate. -/
theorem wide_circular_connections_lower_of_published
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0 < β) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ k : ℕ, 2 ≤ k → ∃ δ : ℝ, 0 < δ ∧
      ∀ (w : ℕ), 1 ≤ w → B₀ ≤ w → ∀ (r : ℤ), 2*(K*w+1) < r →
        (w:ℤ)+(K*w+1) < (k*(2*w):ℕ)-2 →
        ∀ (Λ : Finset Site),
          cardinalSupport (r-(K*w+1)) (r+k*(2*w)-2+(K*w+1)) (K*w+1) ⊆ Λ →
          ∀ mesh radius : ℝ, 0 < mesh →
            2*mesh*(r+2*(K*w+1)) ≤ radius →
            4*radius < mesh*(r+k*(2*w)-2-(K*w+1)) →
            δ ≤ probability (sourceLaw Λ) (WideCircularConnections r (r+k*(2*w)-2) w (K*w+1) mesh radius) := by
  obtain ⟨K,hK,hlower⟩ := wide_cardinal_lower_of_published boundaryInput hRSW hupper hβ
  refine ⟨K,hK,?_⟩
  intro k hk
  obtain ⟨c,hc,hcLower⟩ := hlower k hk
  refine ⟨c^32,pow_pos hc _,?_⟩
  intro w hw hBw r hwidth hgap Λ hΛ mesh radius hm hinner houter
  have hprob := hcLower w hw hBw r hwidth Λ (circularSeamSites Λ mesh radius) hΛ
  apply hprob.trans (CanonicalRadialLaw.probability_mono _ ?_)
  intro ω hω
  exact wide_requirements_imply_circular_connections r (r+k*(2*w)-2) w (K*w+1)
    (by nlinarith) hwidth (by push_cast at hgap ⊢; omega) hΛ mesh radius hm
    (by push_cast; exact hinner) (by push_cast; exact houter) ω hω

#print axioms wide_requirements_imply_circular_connections
#print axioms wide_circular_connections_lower_of_published

end ExceptionalTimes.PairSquareSewing
