import ExceptionalTimes.KruskalComponents
import ExceptionalTimes.SortedKruskal
import Mathlib.Tactic.FieldSimp

/-! Exact multiplicative accounting for the literal root-contracted greedy
execution. The dictionary with maximal positive geometric lives is separate. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.KruskalLedger

open SimpleGraph RootKruskal KruskalComponents

variable {V : Type*} [Fintype V]

noncomputable def endingFactor (G : SimpleGraph V) (fixed : V → Prop)
    (p : ℝ → ℝ) (birthAt : Set V → ℝ) (ell : ℝ) (a : V) : ℝ :=
  if ∀ r ∈ component (contracted G fixed) a, ¬ fixed r
  then p (birthAt (component (contracted G fixed) a)) / p ell else 1

theorem accepted_balance (G : SimpleGraph V) (fixed : V → Prop) (u v : V)
    (hn : ¬ (contracted G fixed).Reachable u v) (p : ℝ → ℝ)
    (birthAt : Set V → ℝ) (ell : ℝ) (hp : p ell ≠ 0) :
    let U := component (contracted G fixed) u
    let W := component (contracted G fixed) v
    (endingFactor G fixed p birthAt ell u * endingFactor G fixed p birthAt ell v) *
      (∏ S ∈ ungrounded (step fixed G (u,v)) fixed,
        p (if S = U ∪ W then ell else birthAt S)) =
      (∏ S ∈ ungrounded G fixed, p (birthAt S)) / p ell := by
  dsimp only
  let U := component (contracted G fixed) u
  let W := component (contracted G fixed) v
  let rest := ((ungrounded G fixed).erase U).erase W
  have hne : U ≠ W := fun h => hn ((component_eq_iff _ _ _).mp h)
  have hunion : U ∪ W ∉ rest := by
    intro h
    have h' := (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
    exact union_not_mem_components _ u v hn (Finset.mem_filter.mp h').1
  have hrest : (∏ S ∈ rest, p (if S = U ∪ W then ell else birthAt S)) =
      ∏ S ∈ rest, p (birthAt S) := by
    apply Finset.prod_congr rfl
    intro S hS
    have hneS : S ≠ U ∪ W := fun h => hunion (h ▸ hS)
    rw [ite_eq_right hneS]
  rw [ungrounded_step G fixed u v hn]
  change ((if ∀ r ∈ U, ¬ fixed r then p (birthAt U) / p ell else 1) *
    (if ∀ r ∈ W, ¬ fixed r then p (birthAt W) / p ell else 1)) *
    (∏ S ∈ (if (∀ r ∈ U, ¬ fixed r) ∧ (∀ r ∈ W, ¬ fixed r)
      then insert (U ∪ W) rest else rest), p (if S = U ∪ W then ell else birthAt S)) = _
  by_cases hU : ∀ r ∈ U, ¬ fixed r
  · have hUm : U ∈ ungrounded G fixed := (mem_ungrounded _ _ _).mpr hU
    have hprodU := Finset.mul_prod_erase (ungrounded G fixed) (fun S => p (birthAt S)) hUm
    by_cases hW : ∀ r ∈ W, ¬ fixed r
    · have hWm : W ∈ (ungrounded G fixed).erase U :=
        Finset.mem_erase.mpr ⟨hne.symm, (mem_ungrounded _ _ _).mpr hW⟩
      have hprodW := Finset.mul_prod_erase ((ungrounded G fixed).erase U) (fun S => p (birthAt S)) hWm
      rw [ite_eq_left hU, ite_eq_left hW, ite_eq_left ⟨hU, hW⟩,
        Finset.prod_insert hunion, ite_eq_left rfl, hrest, ← hprodU, ← hprodW]
      change _ = (p (birthAt U) * (p (birthAt W) * ∏ S ∈ rest, p (birthAt S))) / p ell
      field_simp [hp]
    · have hWm : W ∉ (ungrounded G fixed).erase U := fun h =>
        hW ((mem_ungrounded _ _ _).mp (Finset.mem_erase.mp h).2)
      have hrestEq : rest = (ungrounded G fixed).erase U := Finset.erase_eq_of_notMem hWm
      rw [ite_eq_left hU, ite_eq_right hW, ite_eq_right (fun h => hW h.2), hrest, hrestEq, ← hprodU]
      ring
  · have hW := (accepted_has_ungrounded_side G fixed u v hn).resolve_left hU
    have hUm : U ∉ ungrounded G fixed := fun h => hU ((mem_ungrounded _ _ _).mp h)
    have hrestEq : rest = (ungrounded G fixed).erase W := by
      dsimp only [rest]
      rw [Finset.erase_eq_of_notMem hUm]
    have hprodW := Finset.mul_prod_erase (ungrounded G fixed) (fun S => p (birthAt S))
      ((mem_ungrounded _ _ _).mpr hW)
    rw [ite_eq_right hU, ite_eq_left hW, ite_eq_right (fun h => hU h.1), hrest, hrestEq, ← hprodW]
    ring

/-- Birth times maintained by the actual sequential component update. A new
rootless union starts at the accepted edge length; surviving pieces keep theirs. -/
noncomputable def birthAt (fixed : V → Prop) (cutoff : ℝ) (length : V × V → ℝ) :
    List (V × V) → Set V → ℝ
  | [], _ => cutoff
  | e :: es, S =>
      if (contracted (greedy fixed es) fixed).Reachable e.1 e.2 then birthAt fixed cutoff length es S
      else if S = component (contracted (greedy fixed es) fixed) e.1 ∪
          component (contracted (greedy fixed es) fixed) e.2
        then length e else birthAt fixed cutoff length es S

/-- Product of the ratios contributed when actual rootless components end. -/
noncomputable def completedFactor (fixed : V → Prop) (cutoff : ℝ)
    (length : V × V → ℝ) (p : ℝ → ℝ) : List (V × V) → ℝ
  | [] => 1
  | e :: es =>
      if (contracted (greedy fixed es) fixed).Reachable e.1 e.2 then completedFactor fixed cutoff length p es
      else completedFactor fixed cutoff length p es *
        (endingFactor (greedy fixed es) fixed p (birthAt fixed cutoff length es) (length e) e.1 *
          endingFactor (greedy fixed es) fixed p (birthAt fixed cutoff length es) (length e) e.2)

/-- Product over precisely the accepted ordinary candidates. -/
noncomputable def acceptedProduct (fixed : V → Prop) (length : V × V → ℝ) (p : ℝ → ℝ) :
    List (V × V) → ℝ
  | [] => 1
  | e :: es => if (contracted (greedy fixed es) fixed).Reachable e.1 e.2
      then acceptedProduct fixed length p es else acceptedProduct fixed length p es * p (length e)

/-- Exact telescoping invariant, valid for any finite candidate order. Thus
tied edge lengths are processed without requiring a distinctness assumption. -/
theorem ledger_invariant (fixed : V → Prop) (cutoff : ℝ) (length : V × V → ℝ)
    (p : ℝ → ℝ) (hp : ∀ t, p t ≠ 0) (es : List (V × V)) :
    completedFactor fixed cutoff length p es *
      (∏ S ∈ ungrounded (greedy fixed es) fixed, p (birthAt fixed cutoff length es S)) =
      p cutoff ^ Fintype.card {a // ¬ fixed a} / acceptedProduct fixed length p es := by
  induction es with
  | nil => simp [completedFactor, acceptedProduct, greedy, birthAt, ungrounded_bot_card]
  | cons e es ih =>
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · simpa only [completedFactor, acceptedProduct, birthAt, greedy, step, ite_eq_left he] using ih
    · simp only [completedFactor, acceptedProduct, birthAt, greedy, ite_eq_right he]
      have hbal := accepted_balance (greedy fixed es) fixed e.1 e.2 he p
        (birthAt fixed cutoff length es) (length e) (hp (length e))
      dsimp only at hbal
      rw [mul_assoc, hbal, ← mul_div_assoc, ih, div_div]

/-- Termination at a scale where p=1 contributes no terminal factor for
surviving rootless components. -/
theorem terminal_ledger (fixed : V → Prop) (cutoff stop : ℝ) (length : V × V → ℝ)
    (p : ℝ → ℝ) (hp : ∀ t, p t ≠ 0) (hstop : p stop = 1) (es : List (V × V)) :
    completedFactor fixed cutoff length p es *
      (∏ S ∈ ungrounded (greedy fixed es) fixed, p (birthAt fixed cutoff length es S) / p stop) =
      p cutoff ^ Fintype.card {a // ¬ fixed a} / acceptedProduct fixed length p es := by
  simpa only [hstop, div_one] using ledger_invariant fixed cutoff length p hp es

omit [Fintype V] in
theorem edgeFinset_single_edge (u v : V) (huv : u ≠ v) :
    (edge u v).edgeFinset = {s(u,v)} := by
  ext e
  simp only [mem_edgeFinset, edgeSet_edge, Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    subst e
    exact ⟨rfl, by simpa using huv⟩

omit [Fintype V] in
theorem edgeFinset_congr (G H : SimpleGraph V) [Fintype G.edgeSet] [Fintype H.edgeSet]
    (h : G = H) : G.edgeFinset = H.edgeFinset := by
  ext e
  simp only [mem_edgeFinset]
  rw [h]

/-- No candidate multiplicity remains: the accepted product is exactly the
product over the actual unordered edge set of the recorded graph. -/
theorem acceptedProduct_eq_graphProduct (fixed : V → Prop) (length : Sym2 V → ℝ)
    (p : ℝ → ℝ) (es : List (V × V)) :
    acceptedProduct fixed (fun e => length s(e.1,e.2)) p es =
      ∏ e ∈ (greedy fixed es).edgeFinset, p (length e) := by
  induction es with
  | nil =>
    have hempty : (greedy fixed []).edgeFinset = ∅ := by
      ext e
      simp only [mem_edgeFinset, greedy, edgeSet_bot, Set.mem_empty_iff_false, Finset.notMem_empty]
    simp only [acceptedProduct, hempty, Finset.prod_empty]
  | cons e es ih =>
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · have hG : greedy fixed (e :: es) = greedy fixed es := by simp only [greedy, step, ite_eq_left he]
      rw [acceptedProduct, ite_eq_left he, edgeFinset_congr _ _ hG]
      exact ih
    · have hne : e.1 ≠ e.2 := fun h => he (h ▸ Reachable.rfl)
      have hnmem : s(e.1,e.2) ∉ (greedy fixed es).edgeFinset := fun h =>
        he (((mem_edgeFinset.mp h : (greedy fixed es).Adj e.1 e.2).reachable).mono le_sup_left)
      have hG : greedy fixed (e :: es) = greedy fixed es ⊔ edge e.1 e.2 := by
        simp only [greedy, step, ite_eq_right he]
      rw [acceptedProduct, ite_eq_right he, edgeFinset_congr _ _ hG]
      simp only [edgeFinset_sup,
        edgeFinset_single_edge _ _ hne, Finset.union_singleton, Finset.prod_insert hnmem, ih]
      rw [mul_comm]

/-- The right side is the graph product for precisely the accepted edges below
the stopping threshold, rather than the full forest's long edges. -/
theorem terminal_sorted_ledger {X : Type*} [PseudoMetricSpace X]
    (fixed : V → Prop) (position : V → X) (cutoff stop : ℝ)
    (p : ℝ → ℝ) (hp : ∀ t, p t ≠ 0) (hstop : p stop = 1) :
    let es := (SortedKruskal.sortedEdges position cutoff).filter
      (fun e => SortedKruskal.length position cutoff e < stop)
    completedFactor fixed cutoff (SortedKruskal.length position cutoff) p es *
      (∏ S ∈ ungrounded (greedy fixed es) fixed,
        p (birthAt fixed cutoff (SortedKruskal.length position cutoff) es S) / p stop) =
      p cutoff ^ Fintype.card {a // ¬ fixed a} /
        ∏ e ∈ (greedy fixed (SortedKruskal.sortedEdges position cutoff) ⊓
          threshold position cutoff stop).edgeFinset,
          p (ForestGeometry.clippedEdgeLength position cutoff e) := by
  dsimp only
  rw [terminal_ledger fixed cutoff stop _ p hp hstop]
  congr 1
  have he := SortedKruskal.greedy_filter_eq_inf fixed position cutoff stop _
    (SortedKruskal.sortedEdges_pairwise position cutoff)
  rw [← edgeFinset_congr _ _ he]
  exact acceptedProduct_eq_graphProduct fixed (ForestGeometry.clippedEdgeLength position cutoff) p _

#print axioms accepted_balance
#print axioms ledger_invariant
#print axioms terminal_ledger
#print axioms acceptedProduct_eq_graphProduct
#print axioms terminal_sorted_ledger

end ExceptionalTimes.KruskalLedger
