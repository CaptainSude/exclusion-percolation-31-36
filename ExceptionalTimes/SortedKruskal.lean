import ExceptionalTimes.KruskalLives
import Mathlib.Data.List.Sort

/-! One globally sorted recorded forest, with exact compatibility at every
threshold. This permits charging the same recorded edges throughout their
successive ancestor lives. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.SortedKruskal

open RootKruskal SimpleGraph

variable {V X : Type*} [PseudoMetricSpace X]

noncomputable def length (position : V → X) (cutoff : ℝ) (e : V × V) : ℝ :=
  max (dist (position e.1) (position e.2)) cutoff

theorem greedy_le_processed (fixed : V → Prop) (es : List (V × V)) :
    greedy fixed es ≤ processed es := by
  induction es with
  | nil => exact le_rfl
  | cons e es ih =>
    simp only [greedy, step]
    split_ifs
    · exact ih.trans le_sup_left
    · exact sup_le_sup_right ih _

theorem edge_le_threshold (position : V → X) {cutoff t : ℝ} {e : V × V}
    (he : length position cutoff e < t) : edge e.1 e.2 ≤ threshold position cutoff t := by
  intro a b hab
  rcases (edge_adj e.1 e.2 a b).mp hab with ⟨h | h, hne⟩
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨hne, he⟩
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨hne, by simpa only [length, _root_.dist_comm] using he⟩

theorem edge_inf_threshold (position : V → X) {cutoff t : ℝ} {e : V × V}
    (he : ¬ length position cutoff e < t) : edge e.1 e.2 ⊓ threshold position cutoff t = ⊥ := by
  apply le_antisymm _ bot_le
  intro a b hab
  rcases (edge_adj e.1 e.2 a b).mp hab.1 with ⟨h | h, hne⟩
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (he hab.2.2)
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (he (by simpa only [length, _root_.dist_comm] using hab.2.2))

theorem processed_le_threshold (position : V → X) (cutoff t : ℝ) (es : List (V × V))
    (h : ∀ e ∈ es, length position cutoff e < t) : processed es ≤ threshold position cutoff t := by
  induction es with
  | nil => exact bot_le
  | cons e es ih =>
    exact sup_le (ih (fun f hf => h f (List.mem_cons_of_mem e hf)))
      (edge_le_threshold position (h e (List.mem_cons_self ..)))

/-- A sorted greedy run restricted to short edges is exactly the greedy run
on its short-edge prefix (stored in reverse order by the recursive algorithm). -/
theorem greedy_filter_eq_inf (fixed : V → Prop) (position : V → X) (cutoff t : ℝ)
    (es : List (V × V))
    (hsort : es.Pairwise (fun e f => length position cutoff f ≤ length position cutoff e)) :
    greedy fixed (es.filter (fun e => length position cutoff e < t)) =
      greedy fixed es ⊓ threshold position cutoff t := by
  induction es with
  | nil => simp [greedy]
  | cons e es ih =>
    by_cases he : length position cutoff e < t
    · have hall : ∀ f ∈ e::es, length position cutoff f < t := by
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact he
        · exact ((List.pairwise_cons.mp hsort).1 f hf).trans_lt he
      have hfilt : (e::es).filter (fun e => length position cutoff e < t) = e::es := by
        apply List.filter_eq_self.mpr
        intro f hf
        exact decide_eq_true (hall f hf)
      rw [hfilt, inf_eq_left.mpr ((greedy_le_processed fixed _).trans
        (processed_le_threshold position cutoff t _ hall))]
    · rw [List.filter_cons]
      simp only [decide_eq_false he, Bool.false_eq_true, ↓reduceIte]
      rw [ih (List.pairwise_cons.mp hsort).2]
      simp only [greedy, step]
      split_ifs
      · rfl
      · rw [inf_sup_right, edge_inf_threshold position he, sup_bot_eq]

noncomputable def sortedEdges [Fintype V] (position : V → X) (cutoff : ℝ) : List (V × V) :=
  Finset.univ.toList.mergeSort (fun e f => decide (length position cutoff f ≤ length position cutoff e))

theorem sortedEdges_pairwise [Fintype V] (position : V → X) (cutoff : ℝ) :
    (sortedEdges position cutoff).Pairwise
      (fun e f => length position cutoff f ≤ length position cutoff e) := by
  have h := List.pairwise_mergeSort
    (le := fun e f : V × V => decide (length position cutoff f ≤ length position cutoff e))
    (fun a b c hab hbc => by simpa using (of_decide_eq_true hbc).trans (of_decide_eq_true hab))
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
    (Finset.univ.toList : List (V × V))
  simpa only [sortedEdges, decide_eq_true_eq] using h

theorem mem_sortedEdges [Fintype V] (position : V → X) (cutoff : ℝ) (e : V × V) :
    e ∈ sortedEdges position cutoff := by
  rw [sortedEdges, List.mem_mergeSort]
  simp

theorem processed_sorted_below [Fintype V] (position : V → X) (cutoff t : ℝ) :
    processed ((sortedEdges position cutoff).filter (fun e => length position cutoff e < t)) =
      threshold position cutoff t := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  rw [processed_adj]
  constructor
  · rintro ⟨e, he, hab⟩
    exact edge_le_threshold position (of_decide_eq_true (List.mem_filter.mp he).2) hab
  · intro hab
    refine ⟨(a,b), ?_, (edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩, hab.1⟩⟩
    exact List.mem_filter.mpr ⟨mem_sortedEdges position cutoff _, decide_eq_true hab.2⟩

/-- Every threshold component is carried by the short edges of one common
recorded forest, not a different forest chosen separately at each scale. -/
theorem sorted_threshold_reachable [Fintype V] (fixed : V → Prop) (position : V → X)
    (cutoff t : ℝ) :
    (contracted (greedy fixed (sortedEdges position cutoff) ⊓ threshold position cutoff t) fixed).Reachable =
      (contracted (threshold position cutoff t) fixed).Reachable := by
  rw [← greedy_filter_eq_inf fixed position cutoff t _ (sortedEdges_pairwise position cutoff),
    contracted_greedy_reachable, processed_sorted_below]

#print axioms greedy_filter_eq_inf
#print axioms sorted_threshold_reachable

end ExceptionalTimes.SortedKruskal
