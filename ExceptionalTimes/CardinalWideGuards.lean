import ExceptionalTimes.CardinalTrackGeometry

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open AnnularCollars

/-- The guard's outer radius is independent of the crossing width. This
allows the wide annuli supplied by the proved static circuit estimate. -/
theorem cardinalTrack_subset_wide (r R : ℤ) (w U : ℕ) (hwU : w ≤ U) (i : Fin 4) :
    (cardinalTrack r R w i).domain ⊆ (cardinalTrack (r-U) (R+U) U i).domain := by
  intro z hz
  fin_cases i <;>
    simp [cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] at hz ⊢ <;> omega

theorem cardinalEndpoint_wide_box_subset (r R : ℤ) (U : ℕ) (hrR : r ≤ R)
    (i : Fin 4) (t : ℤ) (ht : t=r ∨ t=R) {z : Site}
    (hz : z-cardinalEndpoint t i ∈ latticeBox U) :
    z ∈ (cardinalTrack (r-U) (R+U) U i).domain := by
  rcases ht with rfl | rfl <;> fin_cases i <;>
    simp [cardinalEndpoint,latticeBox,cardinalTrack,horizontalTrack,verticalTrack,
      axialRectangleSites] at hz ⊢ <;> omega

theorem cardinal_wide_pairwise (r R : ℤ) (U : ℕ) (hgap : 2*U < r)
    {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (cardinalTrack (r-U) (R+U) U i).domain
      (cardinalTrack (r-U) (R+U) U j).domain := by
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals
    simp [cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] at hzi hzj
    omega

theorem cardinal_wide_guards_separated (r R : ℤ) (w U : ℕ)
    (hgap : (w:ℤ)+U < R-r) (i : Fin 4) {u v : Site}
    (hu : u-cardinalEndpoint r i ∈ latticeBox w)
    (hv : v-cardinalEndpoint R i ∈ latticeBox w) :
    v-cardinalEndpoint r i ∉ latticeBox U ∧ u-cardinalEndpoint R i ∉ latticeBox U := by
  constructor <;> intro h <;> fin_cases i <;>
    simp [cardinalEndpoint,latticeBox] at hu hv h <;> omega

theorem cardinal_wide_guarded_join (r R : ℤ) (w U : ℕ) (hwU : w ≤ U)
    (hgap : (w:ℤ)+U < R-r) (i : Fin 4) (color : Bool) (ω : Configuration)
    (C D : SurroundingCircuit w U)
    (hC : ∀ z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support, ω z=color)
    (hD : ∀ z ∈ (shiftedCircuit (cardinalEndpoint R i) D).support, ω z=color)
    (h : (cardinalTrack r R w i).ColorCrossing color ω)
    {x y : Site} (hx : x ∈ (shiftedCircuit (cardinalEndpoint r i) C).support)
    (hy : y ∈ (shiftedCircuit (cardinalEndpoint R i) D).support) :
    ∃ q : triangularGraph.Walk x y, q.IsPath ∧
      ∀ z ∈ q.support, z ∈ (cardinalTrack (r-U) (R+U) U i).domain ∧ ω z=color := by
  obtain ⟨u,hu,v,hv,p,hp⟩ := cardinalCrossing_endpoints r R w i color ω h
  have hsep := cardinal_wide_guards_separated r R w U hgap i hu hv
  obtain ⟨a,ha,haC⟩ := shiftedCircuit_hits _ C hu hsep.1 p
  obtain ⟨b,hb,hbD⟩ := shiftedCircuit_hits _ D hv hsep.2 p.reverse
  rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hb
  obtain ⟨q₀,hq₀⟩ := walk_between_support (shiftedCircuit (cardinalEndpoint r i) C) hx haC
  obtain ⟨q₁,hq₁⟩ := walk_between_support p ha hb
  obtain ⟨q₂,hq₂⟩ := walk_between_support (shiftedCircuit (cardinalEndpoint R i) D) hbD hy
  let q := (q₀.append q₁).append q₂
  refine ⟨q.toPath.val,q.toPath.property,?_⟩
  intro z hz
  have hz' := q.support_toPath_subset_support hz
  simp only [q,SimpleGraph.Walk.mem_support_append_iff] at hz'
  rcases hz' with (hz₀ | hz₁) | hz₂
  · have hm := hq₀ z hz₀
    exact ⟨cardinalEndpoint_wide_box_subset r R U (by omega) i r (Or.inl rfl)
      (shiftedCircuit_inside _ C hm),hC z hm⟩
  · exact ⟨cardinalTrack_subset_wide r R w U hwU i (hp z (hq₁ z hz₁)).1,
      (hp z (hq₁ z hz₁)).2⟩
  · have hm := hq₂ z hz₂
    exact ⟨cardinalEndpoint_wide_box_subset r R U (by omega) i R (Or.inr rfl)
      (shiftedCircuit_inside _ D hm),hD z hm⟩

#print axioms cardinal_wide_pairwise
#print axioms cardinal_wide_guarded_join

end ExceptionalTimes.PairSquareSewing
