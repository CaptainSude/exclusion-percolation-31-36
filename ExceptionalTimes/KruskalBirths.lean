import ExceptionalTimes.KruskalLedger
import ExceptionalTimes.ForestLifeGeometry

/-! The birth recorded by the actual sorted greedy execution is the maximum
of the cutoff and its component's internal accepted edge lengths. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.KruskalBirths

open SimpleGraph RootKruskal KruskalComponents KruskalLedger ForestLifeGeometry

variable {V : Type*} [Fintype V]

theorem reachable_of_same_ungrounded {G : SimpleGraph V} {fixed : V → Prop} {S : Set V}
    (hS : S ∈ ungrounded G fixed) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (contracted G fixed).Reachable x y := by
  obtain ⟨a, ha⟩ := (mem_components _ _).mp (Finset.mem_filter.mp hS).1
  have hx' : (contracted G fixed).Reachable a x := by
    change x ∈ component (contracted G fixed) a
    rwa [ha]
  have hy' : (contracted G fixed).Reachable a y := by
    change y ∈ component (contracted G fixed) a
    rwa [ha]
  exact hx'.symm.trans hy'

theorem ordinary_reachable_of_same_ungrounded {G : SimpleGraph V} {fixed : V → Prop} {S : Set V}
    (hS : S ∈ ungrounded G fixed) {x y : V} (hx : x ∈ S) (hy : y ∈ S) : G.Reachable x y := by
  apply ordinary_reachable_of_rootless G fixed (reachable_of_same_ungrounded hS hx hy)
  intro r hr hxr
  obtain ⟨a, ha⟩ := (mem_components _ _).mp (Finset.mem_filter.mp hS).1
  have hx' : (contracted G fixed).Reachable a x := by
    change x ∈ component (contracted G fixed) a
    rwa [ha]
  have hrS : r ∈ S := by
    rw [← ha]
    exact hx'.trans hxr
  exact (Finset.mem_filter.mp hS).2 r hrS hr

omit [Fintype V] in
theorem accepted_edge_length_le (fixed : V → Prop) (length : Sym2 V → ℝ)
    (es : List (V × V)) {M : ℝ} (hbound : ∀ e ∈ es, length s(e.1,e.2) ≤ M)
    {x y : V} (hxy : (greedy fixed es).Adj x y) : length s(x,y) ≤ M := by
  obtain ⟨e, he, hedge⟩ := (processed_adj es x y).mp (SortedKruskal.greedy_le_processed fixed es hxy)
  rcases (edge_adj e.1 e.2 x y).mp hedge with ⟨h | h, _⟩
  · rcases h with ⟨rfl, rfl⟩
    exact hbound e he
  · rcases h with ⟨rfl, rfl⟩
    simpa only [Sym2.eq_swap] using hbound e he

/-- Exact maximum characterization, including an actual edge attaining the
birth unless the birth equals the microscopic cutoff. -/
theorem birthAt_spec (fixed : V → Prop) (cutoff : ℝ) (length : Sym2 V → ℝ)
    (es : List (V × V))
    (hsort : es.Pairwise (fun e f => length s(f.1,f.2) ≤ length s(e.1,e.2)))
    (hcut : ∀ e ∈ es, cutoff ≤ length s(e.1,e.2))
    {S : Set V} (hS : S ∈ ungrounded (greedy fixed es) fixed) :
    cutoff ≤ birthAt fixed cutoff (fun e => length s(e.1,e.2)) es S ∧
    (∀ x ∈ S, ∀ y ∈ S, (greedy fixed es).Adj x y →
      length s(x,y) ≤ birthAt fixed cutoff (fun e => length s(e.1,e.2)) es S) ∧
    (birthAt fixed cutoff (fun e => length s(e.1,e.2)) es S = cutoff ∨
      ∃ x ∈ S, ∃ y ∈ S, (greedy fixed es).Adj x y ∧
        length s(x,y) = birthAt fixed cutoff (fun e => length s(e.1,e.2)) es S) := by
  induction es generalizing S with
  | nil =>
    refine ⟨le_rfl, ?_, Or.inl rfl⟩
    intro x _ y _ hxy
    exact False.elim hxy
  | cons e es ih =>
    have hsortTail := (List.pairwise_cons.mp hsort).2
    have hhead := (List.pairwise_cons.mp hsort).1
    have hcutTail : ∀ f ∈ es, cutoff ≤ length s(f.1,f.2) :=
      fun f hf => hcut f (List.mem_cons.mpr (Or.inr hf))
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · have hS' : S ∈ ungrounded (greedy fixed es) fixed := by
        simpa only [greedy, step, ite_eq_left he] using hS
      simpa only [greedy, step, birthAt, ite_eq_left he] using ih hsortTail hcutTail hS'
    · let U := component (contracted (greedy fixed es) fixed) e.1
      let W := component (contracted (greedy fixed es) fixed) e.2
      by_cases hSU : S = U ∪ W
      · have hb : birthAt fixed cutoff (fun e => length s(e.1,e.2)) (e::es) S = length s(e.1,e.2) := by
          rw [birthAt, ite_eq_right he]
          change (if S = U ∪ W then _ else _) = _
          rw [ite_eq_left hSU]
        rw [hb]
        refine ⟨hcut e (List.mem_cons.mpr (Or.inl rfl)), ?_, Or.inr ?_⟩
        · intro x _ y _ hxy
          apply accepted_edge_length_le fixed length (e::es) _ hxy
          intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact le_rfl
          · exact hhead f hf
        · have hne : e.1 ≠ e.2 := fun h => he (h ▸ Reachable.rfl)
          refine ⟨e.1, ?_, e.2, ?_, ?_, rfl⟩
          · rw [hSU]
            exact Or.inl (component_self _ _)
          · rw [hSU]
            exact Or.inr (component_self _ _)
          · change (step fixed (greedy fixed es) e).Adj e.1 e.2
            rw [step, ite_eq_right he]
            exact Or.inr ((edge_adj e.1 e.2 e.1 e.2).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
      · have hS' : S ∈ ungrounded (greedy fixed es) fixed := by
          change S ∈ ungrounded (step fixed (greedy fixed es) (e.1,e.2)) fixed at hS
          rw [ungrounded_step _ _ _ _ he] at hS
          split_ifs at hS with hroots
          · rcases Finset.mem_insert.mp hS with hS | hS
            · exact False.elim (hSU hS)
            · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
          · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hS).2).2
        have hb : birthAt fixed cutoff (fun e => length s(e.1,e.2)) (e::es) S =
            birthAt fixed cutoff (fun e => length s(e.1,e.2)) es S := by
          rw [birthAt, ite_eq_right he]
          change (if S = U ∪ W then _ else _) = _
          rw [ite_eq_right hSU]
        rw [hb]
        obtain ⟨hb0, hbound, hattain⟩ := ih hsortTail hcutTail hS'
        refine ⟨hb0, ?_, ?_⟩
        · intro x hx y hy hxy
          change (step fixed (greedy fixed es) e).Adj x y at hxy
          rw [step, ite_eq_right he] at hxy
          rcases hxy with hxy | hxy
          · exact hbound x hx y hy hxy
          · rcases (edge_adj e.1 e.2 x y).mp hxy with ⟨h | h, _⟩
            · rcases h with ⟨rfl, rfl⟩
              exact False.elim (he (reachable_of_same_ungrounded hS' hx hy))
            · rcases h with ⟨rfl, rfl⟩
              exact False.elim (he (reachable_of_same_ungrounded hS' hy hx))
        · rcases hattain with h | ⟨x, hx, y, hy, hxy, hlen⟩
          · exact Or.inl h
          · refine Or.inr ⟨x, hx, y, hy, ?_, hlen⟩
            change (step fixed (greedy fixed es) e).Adj x y
            rw [step, ite_eq_right he]
            exact Or.inl hxy

#print axioms birthAt_spec

end ExceptionalTimes.KruskalBirths
