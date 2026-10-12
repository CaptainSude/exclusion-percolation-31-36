import ExceptionalTimes.KruskalBirths
import ExceptionalTimes.LifeEndpoints

/-! Realization of a concrete greedy component as an actual positive life
from its internal and leaving edge thresholds. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.LifeRealization

open SimpleGraph RootKruskal SortedKruskal KruskalComponents KruskalBirths KruskalLives
  ForestLifeGeometry ForestGeometry LifeEndpoints

variable {V X : Type*} [Fintype V] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
theorem reachable_stays_in_ungrounded {G : SimpleGraph V} {fixed : V → Prop} {S : Set V}
    (hS : S ∈ ungrounded G fixed) {x y : V} (hx : x ∈ S) (hxy : G.Reachable x y) : y ∈ S := by
  obtain ⟨a, ha⟩ := (mem_components _ _).mp (Finset.mem_filter.mp hS).1
  have hx' : (contracted G fixed).Reachable a x := by
    change x ∈ component (contracted G fixed) a
    rwa [ha]
  rw [← ha]
  exact hx'.trans (hxy.mono le_sup_left)

theorem occurs_of_component_bounds (fixed : V → Prop) (position : V → X)
    (cutoff : ℝ) {G : SimpleGraph V} (hG : G ≤ recorded fixed position cutoff)
    {S : Set V} (hS : S ∈ ungrounded G fixed) {b d t : ℝ} (hbt : b < t) (htd : t < d)
    (hinternal : ∀ x ∈ S, ∀ y ∈ S, (recorded fixed position cutoff).Adj x y →
      clippedEdgeLength position cutoff s(x,y) ≤ b)
    (hleaving : ∀ x ∈ S, ∀ y ∉ S, (recorded fixed position cutoff).Adj x y →
      d ≤ clippedEdgeLength position cutoff s(x,y)) : Occurs fixed position cutoff S t := by
  obtain ⟨a, ha⟩ := (mem_components _ _).mp (Finset.mem_filter.mp hS).1
  have haS : a ∈ S := ha ▸ component_self (contracted G fixed) a
  have hrootless := (Finset.mem_filter.mp hS).2
  have hclosed : ∀ x ∈ S, ∀ y,
      (contracted (recorded fixed position cutoff ⊓ threshold position cutoff t) fixed).Adj x y → y ∈ S := by
    intro x hx y hxy
    rcases hxy with hxy | hxy
    · by_contra hy
      have hlen := hleaving x hx y hy hxy.1
      have hlen' : clippedEdgeLength position cutoff s(x,y) < t := hxy.2.2
      linarith
    · exact False.elim (hrootless x hx hxy.2.1)
  refine ⟨a, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨p⟩ := ordinary_reachable_of_same_ungrounded hS haS hy
    have hsupp : ∀ z ∈ p.support, z ∈ S := fun z hz =>
      reachable_stays_in_ungrounded hS haS ⟨p.takeUntil z hz⟩
    let p' := p.induce S hsupp
    let φ : G.induce S →g (recorded fixed position cutoff ⊓ threshold position cutoff t) := {
      toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        change G.Adj x.val y.val at hxy
        exact ⟨hG hxy, hxy.ne, (hinternal x.val x.property y.val y.property (hG hxy)).trans_lt hbt⟩ }
    have hp : (recorded fixed position cutoff ⊓ threshold position cutoff t).Reachable a y := ⟨p'.map φ⟩
    have hh := hp.mono (show recorded fixed position cutoff ⊓ threshold position cutoff t ≤
      contracted (recorded fixed position cutoff ⊓ threshold position cutoff t) fixed from le_sup_left)
    change (contracted (greedy fixed (sortedEdges position cutoff) ⊓ threshold position cutoff t) fixed).Reachable a y at hh
    rw [sorted_threshold_reachable] at hh
    exact hh
  · intro y hy
    change (contracted (threshold position cutoff t) fixed).Reachable a y at hy
    rw [← sorted_threshold_reachable fixed position cutoff t] at hy
    exact reachable_stays_of_closed hclosed haS hy

/-- A finite greedy component with matching internal and exit edge witnesses
has exactly the claimed geometric birth and death. -/
theorem actual_life_of_component_bounds (fixed : V → Prop) (position : V → X)
    (cutoff stop : ℝ) {G : SimpleGraph V} (hG : G ≤ recorded fixed position cutoff)
    {S : Set V} (hS : S ∈ ungrounded G fixed) {b d : ℝ}
    (hcut : cutoff ≤ b) (hbd : b < d) (hstop : d ≤ stop)
    (hinternal : ∀ x ∈ S, ∀ y ∈ S, (recorded fixed position cutoff).Adj x y →
      clippedEdgeLength position cutoff s(x,y) ≤ b)
    (hleaving : ∀ x ∈ S, ∀ y ∉ S, (recorded fixed position cutoff).Adj x y →
      d ≤ clippedEdgeLength position cutoff s(x,y))
    (hborn : b = cutoff ∨ ∃ x ∈ S, ∃ y ∈ S, (recorded fixed position cutoff).Adj x y ∧
      clippedEdgeLength position cutoff s(x,y) = b)
    (hends : d = stop ∨ ∃ x ∈ S, ∃ y ∉ S, (recorded fixed position cutoff).Adj x y ∧
      clippedEdgeLength position cutoff s(x,y) = d) :
    (lifeTimes fixed position cutoff stop S).Nonempty ∧
    birth fixed position cutoff stop S = b ∧ death fixed position cutoff stop S = d := by
  have hmem : ∀ t, b < t → t < d → t ∈ lifeTimes fixed position cutoff stop S := by
    intro t hbt htd
    exact ⟨hcut.trans hbt.le, htd.le.trans hstop,
      occurs_of_component_bounds fixed position cutoff hG hS hbt htd hinternal hleaving⟩
  let t₁ := (2*b+d)/3
  let t₂ := (b+2*d)/3
  have ht₁ : b < t₁ ∧ t₁ < d := by dsimp [t₁]; constructor <;> linarith
  have ht₂ : b < t₂ ∧ t₂ < d := by dsimp [t₂]; constructor <;> linarith
  have htimes : (lifeTimes fixed position cutoff stop S).Nonempty := ⟨t₁, hmem t₁ ht₁.1 ht₁.2⟩
  have hbirth : birth fixed position cutoff stop S ≤ t₁ :=
    csInf_le ⟨cutoff, fun _ hr => hr.1⟩ (hmem t₁ ht₁.1 ht₁.2)
  have hdeath : t₂ ≤ death fixed position cutoff stop S :=
    le_csSup ⟨stop, fun _ hr => hr.2.1⟩ (hmem t₂ ht₂.1 ht₂.2)
  have hpositive : birth fixed position cutoff stop S < death fixed position cutoff stop S := by
    have hlt : t₁ < t₂ := by dsimp [t₁, t₂]; linarith
    exact hbirth.trans_lt (hlt.trans_le hdeath)
  have hrootless := (Finset.mem_filter.mp hS).2
  have hbirth_le : birth fixed position cutoff stop S ≤ b := by
    apply birth_le_of_internal_le htimes hrootless hpositive hcut
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact hinternal x ((Finset.mem_filter.mp he).2 x (by simp))
        y ((Finset.mem_filter.mp he).2 y (by simp)) (mem_edgeFinset.mp (Finset.mem_filter.mp he).1)
  have hbirth_ge : b ≤ birth fixed position cutoff stop S := by
    rcases hborn with rfl | ⟨x, hx, y, hy, hxy, hlen⟩
    · exact cutoff_le_birth htimes
    · rw [← hlen]
      apply ForestCharge.internal_edge_length_le_birth htimes hrootless hpositive
      apply Finset.mem_filter.mpr
      refine ⟨mem_edgeFinset.mpr hxy, ?_⟩
      intro z hz
      have hz' : z = x ∨ z = y := by simpa using hz
      rcases hz' with rfl | rfl
      · exact hx
      · exact hy
  have hdeath_ge : d ≤ death fixed position cutoff stop S :=
    le_death_of_crossing_le htimes hrootless hpositive hstop hleaving
  have hdeath_le : death fixed position cutoff stop S ≤ d := by
    rcases hends with rfl | ⟨x, hx, y, hy, hxy, hlen⟩
    · exact death_le_stop htimes
    · rw [← hlen]
      exact (life_external_distance htimes hpositive hx hy).trans (le_max_left _ _)
  exact ⟨htimes, le_antisymm hbirth_le hbirth_ge, le_antisymm hdeath_le hdeath_ge⟩

#print axioms occurs_of_component_bounds
#print axioms actual_life_of_component_bounds

end ExceptionalTimes.LifeRealization
