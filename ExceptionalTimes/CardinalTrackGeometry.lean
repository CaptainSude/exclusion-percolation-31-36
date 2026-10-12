import ExceptionalTimes.CardinalSewnTracks
import ExceptionalTimes.ContactCrosscutOrder
import ExceptionalTimes.HexCutCycles
import ExceptionalTimes.AnnularCollars

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open Annulus AnnularCollars

def cardinalEndpoint (t : ℤ) (i : Fin 4) : Site := ![(t,0),(0,t),(-t,0),(0,-t)] i

/-- The literal tracks remain between explicit hexagonal cuts. -/
theorem cardinalTrack_hex_bounds (r R w : ℤ) (hw : 0 ≤ w) (hwr : w < r)
    (i : Fin 4) {z : Site} (hz : z ∈ (cardinalTrack r R w i).domain) :
    r ≤ hexRadius z ∧ hexRadius z ≤ R+w := by
  fin_cases i <;>
    simp [cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] at hz
  all_goals
    constructor
    · have hx := le_abs_self z.1
      have hy := le_abs_self z.2
      have hnx := neg_le_abs z.1
      have hny := neg_le_abs z.2
      unfold hexRadius
      omega
    · unfold hexRadius
      rw [max_le_iff,max_le_iff]
      repeat' constructor
      all_goals rw [abs_le]; omega

/-- Enlarging each track by twice its width includes both endpoint
guard boxes and still leaves opposite colors separated when 4w < r. -/
theorem cardinalTrack_subset_enlarged (r R : ℤ) (w : ℕ) (i : Fin 4) :
    (cardinalTrack r R w i).domain ⊆
      (cardinalTrack (r-2*w) (R+2*w) (2*w) i).domain := by
  intro z hz
  fin_cases i <;>
    simp [cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] at hz ⊢ <;> omega

theorem cardinalEndpoint_box_subset (r R : ℤ) (w : ℕ) (hrR : r ≤ R)
    (i : Fin 4) (t : ℤ) (ht : t=r ∨ t=R) {z : Site}
    (hz : z-cardinalEndpoint t i ∈ latticeBox (2*w)) :
    z ∈ (cardinalTrack (r-2*w) (R+2*w) (2*w) i).domain := by
  rcases ht with rfl | rfl <;> fin_cases i <;>
    simp [cardinalEndpoint,latticeBox,cardinalTrack,horizontalTrack,verticalTrack,
      axialRectangleSites] at hz ⊢ <;> omega

theorem cardinal_enlarged_opposite_disjoint (r R : ℤ) (w : ℕ) (hgap : 4*w < r) :
    Disjoint (cardinalBlack (r-2*w) (R+2*w) (2*w))
      (cardinalWhite (r-2*w) (R+2*w) (2*w)) :=
  cardinal_opposite_disjoint _ _ _ (by omega)

/-- Orient each crossing from the inner endpoint patch to the outer
endpoint patch, including the west and south tracks. -/
theorem cardinalCrossing_endpoints (r R : ℤ) (w : ℕ) (i : Fin 4)
    (color : Bool) (ω : Configuration)
    (h : (cardinalTrack r R w i).ColorCrossing color ω) :
    ∃ u, u-cardinalEndpoint r i ∈ latticeBox w ∧
      ∃ v, v-cardinalEndpoint R i ∈ latticeBox w ∧
        ∃ p : triangularGraph.Walk u v,
          (∀ z ∈ p.support, z ∈ (cardinalTrack r R w i).domain ∧ ω z=color) := by
  obtain ⟨u,hu,v,hv,p,hp⟩ := h
  fin_cases i
  · refine ⟨u,?_,v,?_,p,hp⟩
    all_goals
      simp [cardinalTrack,horizontalTrack,axialRectangleSites] at hu hv
      simp [cardinalEndpoint,latticeBox]
      omega
  · refine ⟨u,?_,v,?_,p,hp⟩
    all_goals
      simp [cardinalTrack,verticalTrack,axialRectangleSites] at hu hv
      simp [cardinalEndpoint,latticeBox]
      omega
  · refine ⟨v,?_,u,?_,p.reverse,?_⟩
    · simp [cardinalTrack,horizontalTrack,axialRectangleSites] at hu hv
      simp [cardinalEndpoint,latticeBox]
      omega
    · simp [cardinalTrack,horizontalTrack,axialRectangleSites] at hu hv
      simp [cardinalEndpoint,latticeBox]
      omega
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hp
  · refine ⟨v,?_,u,?_,p.reverse,?_⟩
    · simp [cardinalTrack,verticalTrack,axialRectangleSites] at hu hv
      simp [cardinalEndpoint,latticeBox]
      omega
    · simp [cardinalTrack,verticalTrack,axialRectangleSites] at hu hv
      simp [cardinalEndpoint,latticeBox]
      omega
    · simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hp

theorem cardinalEndpoint_boxes_separated (r R : ℤ) (w : ℕ) (hgap : 3*w < R-r)
    (i : Fin 4) {v : Site} (hv : v-cardinalEndpoint R i ∈ latticeBox w) :
    v-cardinalEndpoint r i ∉ latticeBox (2*w) := by
  intro h
  fin_cases i <;> simp [cardinalEndpoint,latticeBox] at hv h <;> omega

/-- An actual surrounding circuit translated to an arbitrary endpoint
patch; no new topological surrounding premise is introduced. -/
def shiftedCircuit {r R : ℕ} (c : Site) (C : SurroundingCircuit r R) :
    triangularGraph.Walk (translateGraph c C.base) (translateGraph c C.base) :=
  C.walk.map (translateGraph c)

theorem shiftedCircuit_inside {r R : ℕ} (c : Site) (C : SurroundingCircuit r R)
    {z : Site} (hz : z ∈ (shiftedCircuit c C).support) : z-c ∈ latticeBox R := by
  rw [shiftedCircuit,SimpleGraph.Walk.support_map] at hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
  change c+y-c ∈ latticeBox R
  simpa only [add_sub_cancel_left] using C.inside y hy

theorem shiftedCircuit_hits {r R : ℕ} (c : Site) (C : SurroundingCircuit r R)
    {u v : Site} (hu : u-c ∈ latticeBox r) (hv : v-c ∉ latticeBox R)
    (p : triangularGraph.Walk u v) :
    ∃ z ∈ p.support, z ∈ (shiftedCircuit c C).support := by
  have hu' : centerGraph c u ∈ latticeBox r := hu
  have hv' : centerGraph c v ∉ latticeBox R := hv
  obtain ⟨y,hy,hyC⟩ := C.hits hu' hv' (p.map (centerGraph c))
  rw [SimpleGraph.Walk.support_map] at hy
  obtain ⟨z,hz,hzy⟩ := List.mem_map.mp hy
  refine ⟨z,hz,?_⟩
  rw [shiftedCircuit,SimpleGraph.Walk.support_map]
  apply List.mem_map.mpr
  refine ⟨y,hyC,?_⟩
  change c+y=z
  change z-c=y at hzy
  rw [←hzy]
  abel

/-- A cardinal connector really meets its inner surrounding guard. -/
theorem cardinalCrossing_hits_inner_guard (r R : ℤ) (w : ℕ)
    (hgap : 3*w < R-r) (i : Fin 4) (color : Bool) (ω : Configuration)
    (C : SurroundingCircuit w (2*w))
    (h : (cardinalTrack r R w i).ColorCrossing color ω) :
    ∃ z ∈ (cardinalTrack r R w i).domain,
      z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support ∧ ω z=color := by
  obtain ⟨u,hu,v,hv,p,hp⟩ := cardinalCrossing_endpoints r R w i color ω h
  obtain ⟨z,hz,hzC⟩ := shiftedCircuit_hits _ C hu
    (cardinalEndpoint_boxes_separated r R w hgap i hv) p
  exact ⟨z,(hp z hz).1,hzC,(hp z hz).2⟩

theorem cardinalEndpoint_boxes_separated_reverse (r R : ℤ) (w : ℕ)
    (hgap : 3*w < R-r) (i : Fin 4) {u : Site}
    (hu : u-cardinalEndpoint r i ∈ latticeBox w) :
    u-cardinalEndpoint R i ∉ latticeBox (2*w) := by
  intro h
  fin_cases i <;> simp [cardinalEndpoint,latticeBox] at hu h <;> omega

theorem walk_between_support {a b x y : Site} (p : triangularGraph.Walk a b)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ q : triangularGraph.Walk x y, ∀ z ∈ q.support, z ∈ p.support := by
  refine ⟨(p.takeUntil x hx).reverse.append (p.takeUntil y hy),?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
    exact p.support_takeUntil_subset_support hx hz
  · exact p.support_takeUntil_subset_support hy hz

/-- Any chosen sites on the two monochromatic guards are joined by a
simple path in the explicit enlarged track. In particular a retained
arm touching either guard is attached to the same connector component.
The guard geometry and all path colors are literal lattice statements. -/
theorem cardinal_guarded_join (r R : ℤ) (w : ℕ) (hgap : 3*w < R-r)
    (i : Fin 4) (color : Bool) (ω : Configuration)
    (C D : SurroundingCircuit w (2*w))
    (hC : ∀ z ∈ (shiftedCircuit (cardinalEndpoint r i) C).support, ω z=color)
    (hD : ∀ z ∈ (shiftedCircuit (cardinalEndpoint R i) D).support, ω z=color)
    (h : (cardinalTrack r R w i).ColorCrossing color ω)
    {x y : Site} (hx : x ∈ (shiftedCircuit (cardinalEndpoint r i) C).support)
    (hy : y ∈ (shiftedCircuit (cardinalEndpoint R i) D).support) :
    ∃ q : triangularGraph.Walk x y, q.IsPath ∧
      ∀ z ∈ q.support,
        z ∈ (cardinalTrack (r-2*w) (R+2*w) (2*w) i).domain ∧ ω z=color := by
  obtain ⟨u,hu,v,hv,p,hp⟩ := cardinalCrossing_endpoints r R w i color ω h
  obtain ⟨a,ha,haC⟩ := shiftedCircuit_hits _ C hu
    (cardinalEndpoint_boxes_separated r R w hgap i hv) p
  obtain ⟨b,hb,hbD⟩ := shiftedCircuit_hits _ D hv
    (cardinalEndpoint_boxes_separated_reverse r R w hgap i hu) p.reverse
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
    exact ⟨cardinalEndpoint_box_subset r R w (by omega) i r (Or.inl rfl)
      (shiftedCircuit_inside _ C hm),hC z hm⟩
  · exact ⟨cardinalTrack_subset_enlarged r R w i (hp z (hq₁ z hz₁)).1,
      (hp z (hq₁ z hz₁)).2⟩
  · have hm := hq₂ z hz₂
    exact ⟨cardinalEndpoint_box_subset r R w (by omega) i R (Or.inr rfl)
      (shiftedCircuit_inside _ D hm),hD z hm⟩

theorem cardinal_enlarged_pairwise (r R : ℤ) (w : ℕ) (hgap : 4*w < r)
    {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (cardinalTrack (r-2*w) (R+2*w) (2*w) i).domain
      (cardinalTrack (r-2*w) (R+2*w) (2*w) j).domain := by
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals
    simp [cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] at hzi hzj
    omega

/-- The four guarded connections are genuinely disjoint, including the
two of the same color. This is stronger than opposite-color separation. -/
theorem cardinal_four_guarded_joins (r R : ℤ) (w : ℕ)
    (hgap : 3*w < R-r) (hwidth : 4*w < r) (ω : Configuration)
    (C D : Fin 4 → SurroundingCircuit w (2*w))
    (hC : ∀ i z, z ∈ (shiftedCircuit (cardinalEndpoint r i) (C i)).support →
      ω z=decide (i.val % 2=0))
    (hD : ∀ i z, z ∈ (shiftedCircuit (cardinalEndpoint R i) (D i)).support →
      ω z=decide (i.val % 2=0))
    (h : ∀ i, (cardinalTrack r R w i).ColorCrossing (decide (i.val % 2=0)) ω)
    (x y : Fin 4 → Site)
    (hx : ∀ i, x i ∈ (shiftedCircuit (cardinalEndpoint r i) (C i)).support)
    (hy : ∀ i, y i ∈ (shiftedCircuit (cardinalEndpoint R i) (D i)).support) :
    ∃ p : ∀ i, triangularGraph.Walk (x i) (y i),
      (∀ i, (p i).IsPath) ∧
      (∀ i z, z ∈ (p i).support →
        z ∈ (cardinalTrack (r-2*w) (R+2*w) (2*w) i).domain ∧
          ω z=decide (i.val % 2=0)) ∧
      (∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support) := by
  have hp := fun i => cardinal_guarded_join r R w hgap i (decide (i.val % 2=0)) ω
    (C i) (D i) (hC i) (hD i) (h i) (hx i) (hy i)
  choose p hpPath hpColor using hp
  refine ⟨p,hpPath,hpColor,?_⟩
  intro i j hij
  apply List.disjoint_left.mpr
  intro z hzi hzj
  exact Finset.disjoint_left.mp (cardinal_enlarged_pairwise r R w hwidth hij)
    (hpColor i z hzi).1 (hpColor j z hzj).1

#print axioms cardinalTrack_hex_bounds
#print axioms cardinal_enlarged_opposite_disjoint
#print axioms cardinalCrossing_hits_inner_guard
#print axioms cardinal_guarded_join
#print axioms cardinal_four_guarded_joins

end ExceptionalTimes.PairSquareSewing
