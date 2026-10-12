import ExceptionalTimes.KruskalLifeDictionary

/-! Literal sequential life records, their exact product, and the fact that
no anchor set is ever recorded twice. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.KruskalEpisodes

open SimpleGraph RootKruskal KruskalComponents KruskalLedger KruskalLifeDictionary

variable {V : Type*} [Fintype V]

structure Episode (V : Type*) where
  anchors : Set V
  born : ℝ
  ends : ℝ

noncomputable def Episode.ratio (p : ℝ → ℝ) (E : Episode V) : ℝ := p E.born / p E.ends

noncomputable def endingSets (G : SimpleGraph V) (fixed : V → Prop) (u v : V) : List (Set V) :=
  [component (contracted G fixed) u, component (contracted G fixed) v].filter
    (fun S => ∀ r ∈ S, ¬ fixed r)

theorem mem_endingSets (G : SimpleGraph V) (fixed : V → Prop) (u v : V) (S : Set V) :
    S ∈ endingSets G fixed u v ↔ S ∈ ungrounded G fixed ∧
      (S = component (contracted G fixed) u ∨ S = component (contracted G fixed) v) := by
  simp only [endingSets, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
  constructor
  · rintro ⟨hside, hr⟩
    refine ⟨?_, hside⟩
    rcases hside with rfl | rfl <;> exact (mem_ungrounded _ _ _).mpr hr
  · rintro ⟨hS, hside⟩
    exact ⟨hside, (Finset.mem_filter.mp hS).2⟩

noncomputable def endingRecords (G : SimpleGraph V) (fixed : V → Prop)
    (births : Set V → ℝ) (ell : ℝ) (u v : V) : List (Episode V) :=
  (endingSets G fixed u v).map (fun S => ⟨S, births S, ell⟩)

theorem endingRecords_product (G : SimpleGraph V) (fixed : V → Prop)
    (births : Set V → ℝ) (ell : ℝ) (u v : V) (p : ℝ → ℝ) :
    ((endingRecords G fixed births ell u v).map (Episode.ratio p)).prod =
      endingFactor G fixed p births ell u * endingFactor G fixed p births ell v := by
  unfold endingRecords endingSets endingFactor
  simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
  split_ifs <;> simp [Episode.ratio]

noncomputable def closedEpisodes (fixed : V → Prop) (cutoff : ℝ) (length : V × V → ℝ) :
    List (V × V) → List (Episode V)
  | [] => []
  | e :: es => if (contracted (greedy fixed es) fixed).Reachable e.1 e.2
      then closedEpisodes fixed cutoff length es
      else closedEpisodes fixed cutoff length es ++ endingRecords (greedy fixed es) fixed
        (birthAt fixed cutoff length es) (length e) e.1 e.2

theorem closedEpisodes_product (fixed : V → Prop) (cutoff : ℝ) (length : V × V → ℝ)
    (p : ℝ → ℝ) (es : List (V × V)) :
    ((closedEpisodes fixed cutoff length es).map (Episode.ratio p)).prod =
      completedFactor fixed cutoff length p es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · simp only [closedEpisodes, completedFactor, ite_eq_left he, ih]
    · simp only [closedEpisodes, completedFactor, ite_eq_right he, List.map_append,
        List.prod_append, ih, endingRecords_product]

noncomputable def allEpisodes (fixed : V → Prop) (cutoff stop : ℝ) (length : V × V → ℝ)
    (es : List (V × V)) : List (Episode V) :=
  closedEpisodes fixed cutoff length es ++ (ungrounded (greedy fixed es) fixed).toList.map
    (fun S => ⟨S, birthAt fixed cutoff length es S, stop⟩)

theorem allEpisodes_product (fixed : V → Prop) (cutoff stop : ℝ) (length : V × V → ℝ)
    (p : ℝ → ℝ) (es : List (V × V)) :
    ((allEpisodes fixed cutoff stop length es).map (Episode.ratio p)).prod =
      completedFactor fixed cutoff length p es *
        ∏ S ∈ ungrounded (greedy fixed es) fixed, p (birthAt fixed cutoff length es S) / p stop := by
  simp only [allEpisodes, List.map_append, List.prod_append, closedEpisodes_product,
    List.map_map, Function.comp_apply, Episode.ratio, Finset.prod_map_toList]

/-- A component that has ended already has a connected point outside it. This
witness persists forever, so the same anchor set cannot become a component again. -/
def Broken (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ x ∈ S, ∃ y ∉ S, G.Reachable x y

omit [Fintype V] in
theorem Broken.mono {G H : SimpleGraph V} {S : Set V} (h : Broken G S) (hGH : G ≤ H) : Broken H S := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨x, hx, y, hy, hxy.mono hGH⟩

theorem Broken.not_mem_components {G : SimpleGraph V} {S : Set V} (h : Broken G S) : S ∉ components G := by
  intro hm
  obtain ⟨a, ha⟩ := (mem_components _ _).mp hm
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  have hax : G.Reachable a x := by
    change x ∈ component G a
    rwa [ha]
  apply hy
  rw [← ha]
  exact hax.trans hxy

theorem ending_broken (G : SimpleGraph V) (fixed : V → Prop) (u v : V)
    (hn : ¬ (contracted G fixed).Reachable u v) {S : Set V} (hS : S ∈ endingSets G fixed u v) :
    Broken (contracted (step fixed G (u,v)) fixed) S := by
  have hne : u ≠ v := fun h => hn (h ▸ Reachable.rfl)
  have hnew : (contracted (step fixed G (u,v)) fixed).Reachable u v := by
    rw [contracted_step_reachable]
    exact (show (contracted G fixed ⊔ edge u v).Adj u v from
      Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)).reachable
  rcases ((mem_endingSets G fixed u v S).mp hS).2 with rfl | rfl
  · exact ⟨u, component_self _ _, v, hn, hnew⟩
  · exact ⟨v, component_self _ _, u, fun h => hn h.symm, hnew.symm⟩

theorem endingSets_nodup (G : SimpleGraph V) (fixed : V → Prop) (u v : V)
    (hn : ¬ (contracted G fixed).Reachable u v) : (endingSets G fixed u v).Nodup := by
  have hne : component (contracted G fixed) u ≠ component (contracted G fixed) v :=
    fun h => hn ((component_eq_iff _ _ _).mp h)
  exact (by simpa using hne : [component (contracted G fixed) u,
    component (contracted G fixed) v].Nodup).filter _

theorem closedEpisodes_invariant (fixed : V → Prop) (cutoff : ℝ) (length : V × V → ℝ)
    (es : List (V × V)) :
    ((closedEpisodes fixed cutoff length es).map Episode.anchors).Nodup ∧
    ∀ E ∈ closedEpisodes fixed cutoff length es, Broken (contracted (greedy fixed es) fixed) E.anchors := by
  induction es with
  | nil => simp [closedEpisodes]
  | cons e es ih =>
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · simpa only [closedEpisodes, greedy, step, ite_eq_left he] using ih
    · have hdis : List.Disjoint ((closedEpisodes fixed cutoff length es).map Episode.anchors)
          (endingSets (greedy fixed es) fixed e.1 e.2) := by
        intro S hOld hNew
        obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hOld
        exact (ih.2 E hE).not_mem_components
          (Finset.mem_filter.mp ((mem_endingSets _ _ _ _ _).mp hNew).1).1
      have hnd := List.nodup_append.mpr ⟨ih.1, endingSets_nodup (greedy fixed es) fixed e.1 e.2 he,
        fun a ha b hb hab => hdis ha (hab.symm ▸ hb)⟩
      constructor
      · simpa only [closedEpisodes, ite_eq_right he, endingRecords, List.map_append,
          List.map_map, Function.comp_def, List.map_id'] using hnd
      · intro E hE
        simp only [closedEpisodes, ite_eq_right he, List.mem_append] at hE
        rcases hE with hE | hE
        · exact (ih.2 E hE).mono (sup_le_sup_right (le_step fixed (greedy fixed es) e) _)
        · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hE
          exact ending_broken (greedy fixed es) fixed e.1 e.2 he hS

theorem allEpisodes_anchors_nodup (fixed : V → Prop) (cutoff stop : ℝ) (length : V × V → ℝ)
    (es : List (V × V)) : ((allEpisodes fixed cutoff stop length es).map Episode.anchors).Nodup := by
  have hi := closedEpisodes_invariant fixed cutoff length es
  have hdis : List.Disjoint ((closedEpisodes fixed cutoff length es).map Episode.anchors)
      (ungrounded (greedy fixed es) fixed).toList := by
    intro S hOld hNew
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hOld
    exact (hi.2 E hE).not_mem_components (Finset.mem_filter.mp (Finset.mem_toList.mp hNew)).1
  have hnd := List.nodup_append.mpr ⟨hi.1, Finset.nodup_toList _,
    fun a ha b hb hab => hdis ha (hab.symm ▸ hb)⟩
  simpa only [allEpisodes, List.map_append, List.map_map, Function.comp_def,
    List.map_id'] using hnd

/-- Every closed record comes from the explicit accepted step that ended it. -/
theorem closed_episode_origin (fixed : V → Prop) (cutoff : ℝ) (length : V × V → ℝ)
    (es : List (V × V)) {E : Episode V} (hE : E ∈ closedEpisodes fixed cutoff length es) :
    ∃ pre e tail, es = pre ++ e :: tail ∧
      ¬ (contracted (greedy fixed tail) fixed).Reachable e.1 e.2 ∧
      E.anchors ∈ ungrounded (greedy fixed tail) fixed ∧
      (E.anchors = component (contracted (greedy fixed tail) fixed) e.1 ∨
        E.anchors = component (contracted (greedy fixed tail) fixed) e.2) ∧
      E.born = birthAt fixed cutoff length tail E.anchors ∧ E.ends = length e := by
  induction es with
  | nil => exact False.elim (List.not_mem_nil hE)
  | cons e es ih =>
    have hlift (h : E ∈ closedEpisodes fixed cutoff length es) :
        ∃ pre f tail, e :: es = pre ++ f :: tail ∧
          ¬ (contracted (greedy fixed tail) fixed).Reachable f.1 f.2 ∧
          E.anchors ∈ ungrounded (greedy fixed tail) fixed ∧
          (E.anchors = component (contracted (greedy fixed tail) fixed) f.1 ∨
            E.anchors = component (contracted (greedy fixed tail) fixed) f.2) ∧
          E.born = birthAt fixed cutoff length tail E.anchors ∧ E.ends = length f := by
      obtain ⟨pre, f, tail, htail, hrest⟩ := ih h
      exact ⟨e :: pre, f, tail, by simp only [List.cons_append, htail], hrest⟩
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · exact hlift (by simpa only [closedEpisodes, ite_eq_left he] using hE)
    · simp only [closedEpisodes, ite_eq_right he, List.mem_append] at hE
      rcases hE with hE | hE
      · exact hlift hE
      · obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hE
        have hs := (mem_endingSets _ _ _ _ _).mp hS
        exact ⟨[], e, es, rfl, he, hs.1, hs.2, rfl, rfl⟩

omit [Fintype V] in
theorem birthAt_le_bound (fixed : V → Prop) (cutoff M : ℝ) (length : V × V → ℝ)
    (es : List (V × V)) (hcut : cutoff ≤ M) (hlen : ∀ e ∈ es, length e ≤ M) (S : Set V) :
    birthAt fixed cutoff length es S ≤ M := by
  induction es with
  | nil => exact hcut
  | cons e es ih =>
    have hi := ih (fun f hf => hlen f (List.mem_cons.mpr (Or.inr hf)))
    unfold birthAt
    split_ifs
    · exact hi
    · exact hlen e (List.mem_cons_self ..)
    · exact hi

omit [Fintype V] in
/-- Filtering a decreasing list at a strict threshold leaves a literal suffix,
including any number of tied edge lengths at the threshold. -/
theorem filter_below_suffix (length : V × V → ℝ) (stop : ℝ) (es : List (V × V))
    (hsort : es.Pairwise (fun e f => length f ≤ length e)) :
    ∃ pre, es = pre ++ es.filter (fun e => length e < stop) := by
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons e es ih =>
    have htail := (List.pairwise_cons.mp hsort).2
    by_cases he : length e < stop
    · have hfilter : es.filter (fun f => length f < stop) = es := by
        apply List.filter_eq_self.mpr
        intro f hf
        exact decide_eq_true (((List.pairwise_cons.mp hsort).1 f hf).trans_lt he)
      exact ⟨[], by simp [he, hfilter]⟩
    · obtain ⟨pre, hp⟩ := ih htail
      refine ⟨e :: pre, ?_⟩
      simp only [List.filter_cons, decide_eq_true_eq, ite_eq_right he, List.cons_append]
      exact congrArg (List.cons e) hp

#print axioms allEpisodes_product
#print axioms allEpisodes_anchors_nodup

end ExceptionalTimes.KruskalEpisodes
