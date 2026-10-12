import ExceptionalTimes.LifeRealization

/-! Positive sequential Kruskal records have exactly the actual geometric
lifeTimes endpoints. The edge lengths and component sets are not assumed. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.KruskalLifeDictionary

open SimpleGraph RootKruskal SortedKruskal KruskalComponents KruskalBirths KruskalLedger
  KruskalLives ForestLifeGeometry ForestGeometry LifeRealization

variable {V X : Type*}

theorem le_step (fixed : V → Prop) (G : SimpleGraph V) (e : V × V) : G ≤ step fixed G e := by
  unfold step
  split_ifs
  · exact le_rfl
  · exact le_sup_left

theorem greedy_le_append (fixed : V → Prop) (pre es : List (V × V)) :
    greedy fixed es ≤ greedy fixed (pre ++ es) := by
  induction pre with
  | nil => exact le_rfl
  | cons e pre ih => exact ih.trans (le_step fixed (greedy fixed (pre ++ es)) e)

theorem filter_below_append_cons (length : V × V → ℝ) (pre es : List (V × V)) (e : V × V)
    (hsort : (pre ++ e :: es).Pairwise (fun e f => length f ≤ length e)) :
    (pre ++ e :: es).filter (fun f => length f < length e) = es.filter (fun f => length f < length e) := by
  have hpre : pre.filter (fun f => length f < length e) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro f hf
    have hle := (List.pairwise_append.mp hsort).2.2 f hf e (List.mem_cons_self ..)
    simpa only [decide_eq_true_eq] using not_lt_of_ge hle
  rw [List.filter_append, hpre]
  simp

variable [Fintype V] [PseudoMetricSpace X]

theorem recorded_below_le_tail (fixed : V → Prop) (position : V → X) (cutoff : ℝ)
    (pre es : List (V × V)) (e : V × V)
    (hfull : sortedEdges position cutoff = pre ++ e :: es) :
    recorded fixed position cutoff ⊓ threshold position cutoff (length position cutoff e) ≤
      greedy fixed es := by
  have hsort : (pre ++ e :: es).Pairwise (fun e f => length position cutoff f ≤ length position cutoff e) :=
    hfull ▸ sortedEdges_pairwise position cutoff
  have htail := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).2
  rw [recorded, ← greedy_filter_eq_inf fixed position cutoff (length position cutoff e) _
    (sortedEdges_pairwise position cutoff), hfull,
    filter_below_append_cons (length position cutoff) pre es e hsort,
    greedy_filter_eq_inf fixed position cutoff _ es htail]
  exact inf_le_left

/-- An actual accepted edge ends a positive sequential component at its exact
geometric death, and the maintained sequential birth is its geometric birth. -/
theorem positive_ending_is_life (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (pre es : List (V × V)) (e : V × V)
    (hfull : sortedEdges position cutoff = pre ++ e :: es)
    (haccept : ¬ (contracted (greedy fixed es) fixed).Reachable e.1 e.2)
    (hstop : length position cutoff e ≤ stop) {S : Set V}
    (hS : S ∈ ungrounded (greedy fixed es) fixed)
    (hside : S = component (contracted (greedy fixed es) fixed) e.1 ∨
      S = component (contracted (greedy fixed es) fixed) e.2)
    (hpositive : birthAt fixed cutoff (length position cutoff) es S < length position cutoff e) :
    (lifeTimes fixed position cutoff stop S).Nonempty ∧
      birth fixed position cutoff stop S = birthAt fixed cutoff (length position cutoff) es S ∧
      death fixed position cutoff stop S = length position cutoff e := by
  have hsort : (pre ++ e :: es).Pairwise (fun e f => length position cutoff f ≤ length position cutoff e) :=
    hfull ▸ sortedEdges_pairwise position cutoff
  have htail := (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).2
  have hspec := birthAt_spec fixed cutoff (clippedEdgeLength position cutoff) es htail
    (fun f _ => le_max_right _ _) hS
  have hnew : greedy fixed (e::es) ≤ recorded fixed position cutoff := by
    rw [recorded, hfull]
    exact greedy_le_append fixed pre (e::es)
  have hG : greedy fixed es ≤ recorded fixed position cutoff :=
    (le_step fixed (greedy fixed es) e).trans hnew
  have hacyclic : (recorded fixed position cutoff).IsAcyclic :=
    greedy_isAcyclic fixed (sortedEdges position cutoff)
  have hinternal : ∀ x ∈ S, ∀ y ∈ S, (recorded fixed position cutoff).Adj x y →
      clippedEdgeLength position cutoff s(x,y) ≤ birthAt fixed cutoff (length position cutoff) es S := by
    intro x hx y hy hxy
    exact hspec.2.1 x hx y hy (edge_of_reachable_in_acyclic_subgraph hacyclic hG hxy
      (ordinary_reachable_of_same_ungrounded hS hx hy))
  have hleaving : ∀ x ∈ S, ∀ y ∉ S, (recorded fixed position cutoff).Adj x y →
      length position cutoff e ≤ clippedEdgeLength position cutoff s(x,y) := by
    intro x hx y hy hxy
    by_contra h
    have hlt := lt_of_not_ge h
    have hold : (greedy fixed es).Adj x y := recorded_below_le_tail fixed position cutoff pre es e hfull
      ⟨hxy, hxy.ne, hlt⟩
    exact hy (reachable_stays_in_ungrounded hS hx hold.reachable)
  have hborn : birthAt fixed cutoff (length position cutoff) es S = cutoff ∨
      ∃ x ∈ S, ∃ y ∈ S, (recorded fixed position cutoff).Adj x y ∧
        clippedEdgeLength position cutoff s(x,y) = birthAt fixed cutoff (length position cutoff) es S := by
    rcases hspec.2.2 with h | ⟨x, hx, y, hy, hxy, hlen⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, y, hy, hG hxy, hlen⟩
  have hne : e.1 ≠ e.2 := fun h => haccept (h ▸ Reachable.rfl)
  have hedge : (recorded fixed position cutoff).Adj e.1 e.2 := by
    apply hnew
    change (step fixed (greedy fixed es) e).Adj e.1 e.2
    rw [step, ite_eq_right haccept]
    exact Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  have hends : length position cutoff e = stop ∨
      ∃ x ∈ S, ∃ y ∉ S, (recorded fixed position cutoff).Adj x y ∧
        clippedEdgeLength position cutoff s(x,y) = length position cutoff e := by
    apply Or.inr
    rcases hside with rfl | rfl
    · exact ⟨e.1, component_self _ _, e.2, haccept, hedge, rfl⟩
    · exact ⟨e.2, component_self _ _, e.1, fun h => haccept h.symm, hedge.symm,
        by simp only [clippedEdgeLength_mk, length, _root_.dist_comm]⟩
  exact actual_life_of_component_bounds fixed position cutoff stop hG hS
    hspec.1 hpositive hstop hinternal hleaving hborn hends

/-- A positive component surviving the actual truncated execution has geometric
death exactly at the stopping scale; rootless trees leave no extra factor. -/
theorem positive_terminal_is_life (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    {S : Set V}
    (hS : S ∈ ungrounded (greedy fixed ((sortedEdges position cutoff).filter
      (fun e => length position cutoff e < stop))) fixed)
    (hpositive : birthAt fixed cutoff (length position cutoff)
      ((sortedEdges position cutoff).filter (fun e => length position cutoff e < stop)) S < stop) :
    (lifeTimes fixed position cutoff stop S).Nonempty ∧
      birth fixed position cutoff stop S = birthAt fixed cutoff (length position cutoff)
        ((sortedEdges position cutoff).filter (fun e => length position cutoff e < stop)) S ∧
      death fixed position cutoff stop S = stop := by
  let es := (sortedEdges position cutoff).filter (fun e => length position cutoff e < stop)
  have hsort : es.Pairwise (fun e f => length position cutoff f ≤ length position cutoff e) :=
    List.Pairwise.filter _ (sortedEdges_pairwise position cutoff)
  have hspec := birthAt_spec fixed cutoff (clippedEdgeLength position cutoff) es hsort
    (fun f _ => le_max_right _ _) hS
  have heq : greedy fixed es = recorded fixed position cutoff ⊓ threshold position cutoff stop :=
    greedy_filter_eq_inf fixed position cutoff stop _ (sortedEdges_pairwise position cutoff)
  have hG : greedy fixed es ≤ recorded fixed position cutoff := by rw [heq]; exact inf_le_left
  have hacyclic : (recorded fixed position cutoff).IsAcyclic :=
    greedy_isAcyclic fixed (sortedEdges position cutoff)
  have hinternal : ∀ x ∈ S, ∀ y ∈ S, (recorded fixed position cutoff).Adj x y →
      clippedEdgeLength position cutoff s(x,y) ≤ birthAt fixed cutoff (length position cutoff) es S := by
    intro x hx y hy hxy
    exact hspec.2.1 x hx y hy (edge_of_reachable_in_acyclic_subgraph hacyclic hG hxy
      (ordinary_reachable_of_same_ungrounded hS hx hy))
  have hleaving : ∀ x ∈ S, ∀ y ∉ S, (recorded fixed position cutoff).Adj x y →
      stop ≤ clippedEdgeLength position cutoff s(x,y) := by
    intro x hx y hy hxy
    by_contra h
    have hold : (greedy fixed es).Adj x y := by
      rw [heq]
      exact ⟨hxy, hxy.ne, lt_of_not_ge h⟩
    exact hy (reachable_stays_in_ungrounded hS hx hold.reachable)
  have hborn : birthAt fixed cutoff (length position cutoff) es S = cutoff ∨
      ∃ x ∈ S, ∃ y ∈ S, (recorded fixed position cutoff).Adj x y ∧
        clippedEdgeLength position cutoff s(x,y) = birthAt fixed cutoff (length position cutoff) es S := by
    rcases hspec.2.2 with h | ⟨x, hx, y, hy, hxy, hlen⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, hx, y, hy, hG hxy, hlen⟩
  exact actual_life_of_component_bounds fixed position cutoff stop hG hS
    hspec.1 hpositive le_rfl hinternal hleaving hborn (Or.inl rfl)

#print axioms positive_ending_is_life
#print axioms positive_terminal_is_life

end ExceptionalTimes.KruskalLifeDictionary
