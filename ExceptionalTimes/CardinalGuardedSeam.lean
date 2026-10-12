import ExceptionalTimes.CardinalTrackGeometry

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open AnnularCollars

theorem cardinalEndpoint_box_inside (r : ℤ) (w m : ℕ) (hr : 0 ≤ r)
    (hm : r+2*w ≤ m) (i : Fin 4) {z : Site}
    (hz : z-cardinalEndpoint r i ∈ latticeBox (2*w)) : z ∈ latticeBox m := by
  fin_cases i <;> simp [cardinalEndpoint,latticeBox] at hz ⊢ <;> omega

theorem cardinalEndpoint_box_outside (R : ℤ) (w m : ℕ)
    (hm : (m:ℤ)+2*w < R) (i : Fin 4) {z : Site}
    (hz : z-cardinalEndpoint R i ∈ latticeBox (2*w)) : z ∉ latticeBox m := by
  intro h
  fin_cases i <;> simp [cardinalEndpoint,latticeBox] at hz h <;> omega

theorem complete_sewnField_inside {Λ : Finset Site} (inside : Finset Site)
    (ω : Sources Λ) (a b : Bool) {z : Site} (hz : z ∈ inside) :
    complete (sewnField inside ω a b) z = complete (if a then ω.2 else ω.1) z := by
  by_cases hzΛ : z ∈ Λ <;> cases a <;> cases b <;>
    simp [complete,sewnField,hz,hzΛ]

theorem complete_sewnField_outside {Λ : Finset Site} (inside : Finset Site)
    (ω : Sources Λ) (a b : Bool) {z : Site} (hz : z ∉ inside) :
    complete (sewnField inside ω a b) z = complete (if b then ω.2 else ω.1) z := by
  by_cases hzΛ : z ∈ Λ <;> cases a <;> cases b <;>
    simp [complete,sewnField,hz,hzΛ]

/-- The inner guard lies entirely in the sewn inner source, by a numeric
margin for the literal square seam. Its witness is shared across both
choices of the outer source. -/
theorem cardinal_inner_guard_sewn {Λ : Finset Site} (r : ℤ) (w m : ℕ)
    (hr : 0 ≤ r) (hm : r+2*w ≤ m) (i : Fin 4) (ω : Sources Λ) (a b : Bool)
    (C : SurroundingCircuit w (2*w)) (color : Bool)
    (hC : ∀ z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support,
      complete (if a then ω.2 else ω.1) z=color) :
    ∀ z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support,
      complete (sewnField (latticeBox m) ω a b) z=color := by
  intro z hz
  rw [complete_sewnField_inside _ _ _ _
    (cardinalEndpoint_box_inside r w m hr hm i (shiftedCircuit_inside _ C hz))]
  exact hC z hz

theorem cardinal_outer_guard_sewn {Λ : Finset Site} (R : ℤ) (w m : ℕ)
    (hm : (m:ℤ)+2*w < R) (i : Fin 4) (ω : Sources Λ) (a b : Bool)
    (D : SurroundingCircuit w (2*w)) (color : Bool)
    (hD : ∀ z ∈ (shiftedCircuit (cardinalEndpoint R i) D).support,
      complete (if b then ω.2 else ω.1) z=color) :
    ∀ z ∈ (shiftedCircuit (cardinalEndpoint R i) D).support,
      complete (sewnField (latticeBox m) ω a b) z=color := by
  intro z hz
  rw [complete_sewnField_outside _ _ _ _
    (cardinalEndpoint_box_outside R w m hm i (shiftedCircuit_inside _ D hz))]
  exact hD z hz

/-- Four pairs of source-indexed guard families and the sixteen actual
sewn connector crossings give four disjoint simple connections in every
sewn field. The inner and outer guards are shared in exactly the source
pattern required by sewing; no independent resampling is used. -/
theorem cardinal_shared_guard_connections {Λ : Finset Site} (r R : ℤ) (w m : ℕ)
    (hwidth : 4*w < r) (hgap : 3*w < R-r)
    (hinner : r+2*w ≤ m) (houter : (m:ℤ)+2*w < R) (ω : Sources Λ)
    (C D : Bool → Fin 4 → SurroundingCircuit w (2*w))
    (hC : ∀ a i z, z ∈ (shiftedCircuit (cardinalEndpoint r i) (C a i)).support →
      complete (if a then ω.2 else ω.1) z=decide (i.val % 2=0))
    (hD : ∀ b i z, z ∈ (shiftedCircuit (cardinalEndpoint R i) (D b i)).support →
      complete (if b then ω.2 else ω.1) z=decide (i.val % 2=0))
    (hcross : ∀ j : Fin 4 × Bool × Bool,
      (cardinalConnector r R w j).event (latticeBox m) ω)
    (x y : Bool → Fin 4 → Site)
    (hx : ∀ a i, x a i ∈ (shiftedCircuit (cardinalEndpoint r i) (C a i)).support)
    (hy : ∀ b i, y b i ∈ (shiftedCircuit (cardinalEndpoint R i) (D b i)).support) :
    ∀ a b, ∃ p : ∀ i, triangularGraph.Walk (x a i) (y b i),
      (∀ i, (p i).IsPath) ∧
      (∀ i z, z ∈ (p i).support →
        z ∈ (cardinalTrack (r-2*w) (R+2*w) (2*w) i).domain ∧
          complete (sewnField (latticeBox m) ω a b) z=decide (i.val % 2=0)) ∧
      (∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support) := by
  intro a b
  apply cardinal_four_guarded_joins r R w hgap hwidth
    (complete (sewnField (latticeBox m) ω a b)) (C a) (D b)
  · intro i
    exact cardinal_inner_guard_sewn r w m (by omega) hinner i ω a b (C a i) _ (hC a i)
  · intro i
    exact cardinal_outer_guard_sewn R w m houter i ω a b (D b i) _ (hD b i)
  · intro i
    exact hcross (i,a,b)
  · exact hx a
  · exact hy b

#print axioms cardinal_shared_guard_connections

end ExceptionalTimes.PairSquareSewing
