import ExceptionalTimes.RootKruskal

/-! Exact finite component updates under the accepted edges of the literal
root-contracted Kruskal algorithm. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.KruskalComponents

open SimpleGraph RootKruskal

variable {V : Type*}

def component (G : SimpleGraph V) (a : V) : Set V := {x | G.Reachable a x}

theorem component_self (G : SimpleGraph V) (a : V) : a ∈ component G a := Reachable.rfl

theorem component_eq_of_reachable {G : SimpleGraph V} {a b : V} (hab : G.Reachable a b) :
    component G a = component G b := by
  ext x
  exact ⟨fun h => hab.symm.trans h, fun h => hab.trans h⟩

theorem component_eq_iff (G : SimpleGraph V) (a b : V) :
    component G a = component G b ↔ G.Reachable a b := by
  constructor
  · intro h
    change b ∈ component G a
    exact h.symm ▸ component_self G b
  · exact component_eq_of_reachable

theorem component_disjoint {G : SimpleGraph V} {a b : V} (hn : ¬ G.Reachable a b) :
    Disjoint (component G a) (component G b) := by
  apply Set.disjoint_left.mpr
  intro x ha hb
  exact hn (ha.trans hb.symm)

theorem component_sup_edge_left (G : SimpleGraph V) (u v : V) :
    component (G ⊔ edge u v) u = component G u ∪ component G v := by
  ext x
  change (G ⊔ edge u v).Reachable u x ↔ G.Reachable u x ∨ G.Reachable v x
  rw [reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨_, h⟩ | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨Reachable.rfl, h⟩)

theorem component_sup_edge_of_unrelated (G : SimpleGraph V) (u v a : V)
    (hu : ¬ G.Reachable a u) (hv : ¬ G.Reachable a v) :
    component (G ⊔ edge u v) a = component G a := by
  ext x
  change (G ⊔ edge u v).Reachable a x ↔ G.Reachable a x
  rw [reachable_sup_edge_iff]
  exact ⟨fun h => h.elim id (fun h => h.elim (fun h => False.elim (hu h.1))
    (fun h => False.elim (hv h.1))), Or.inl⟩

variable [Fintype V]

noncomputable def components (G : SimpleGraph V) : Finset (Set V) :=
  Finset.univ.image (component G)

theorem mem_components (G : SimpleGraph V) (S : Set V) :
    S ∈ components G ↔ ∃ a, component G a = S := by simp [components]

/-- An accepted edge replaces exactly its two old components by their union. -/
theorem components_sup_edge (G : SimpleGraph V) (u v : V) (hn : ¬ G.Reachable u v) :
    components (G ⊔ edge u v) =
      insert (component G u ∪ component G v) ((components G).erase (component G u) |>.erase (component G v)) := by
  have huv : u ≠ v := fun h => hn (h ▸ Reachable.rfl)
  have hnewuv : (G ⊔ edge u v).Reachable u v :=
    (show (G ⊔ edge u v).Adj u v from Or.inr ((edge_adj u v u v).mpr
      ⟨Or.inl ⟨rfl, rfl⟩, huv⟩)).reachable
  ext S
  simp only [Finset.mem_insert, Finset.mem_erase, mem_components]
  constructor
  · rintro ⟨a, rfl⟩
    by_cases hau : G.Reachable a u
    · exact Or.inl ((component_eq_of_reachable (hau.mono le_sup_left)).trans
        (component_sup_edge_left G u v))
    by_cases hav : G.Reachable a v
    · exact Or.inl ((component_eq_of_reachable ((hav.mono le_sup_left).trans hnewuv.symm)).trans
        (component_sup_edge_left G u v))
    rw [component_sup_edge_of_unrelated G u v a hau hav]
    exact Or.inr ⟨fun h => hav ((component_eq_iff G a v).mp h),
      fun h => hau ((component_eq_iff G a u).mp h), ⟨a, rfl⟩⟩
  · rintro (rfl | ⟨hv, hu, a, rfl⟩)
    · exact ⟨u, component_sup_edge_left G u v⟩
    · exact ⟨a, component_sup_edge_of_unrelated G u v a
        (fun h => hu (component_eq_of_reachable h)) (fun h => hv (component_eq_of_reachable h))⟩

/-- Literal ungrounded components, each represented by its anchor set. -/
noncomputable def ungrounded (G : SimpleGraph V) (fixed : V → Prop) : Finset (Set V) :=
  (components (contracted G fixed)).filter (fun S => ∀ r ∈ S, ¬ fixed r)

omit [Fintype V] in
theorem contracted_roots_reachable (G : SimpleGraph V) (fixed : V → Prop)
    {r s : V} (hr : fixed r) (hs : fixed s) : (contracted G fixed).Reachable r s := by
  by_cases hrs : r = s
  · subst s
    exact Reachable.rfl
  · exact (show (contracted G fixed).Adj r s from Or.inr ⟨hrs, hr, hs⟩).reachable

omit [Fintype V] in
/-- Two components that both contain physical roots were already connected
through the virtual sink, so an accepted edge cannot join two grounded pieces. -/
theorem accepted_has_ungrounded_side (G : SimpleGraph V) (fixed : V → Prop) (u v : V)
    (hn : ¬ (contracted G fixed).Reachable u v) :
    (∀ r ∈ component (contracted G fixed) u, ¬ fixed r) ∨
    (∀ r ∈ component (contracted G fixed) v, ¬ fixed r) := by
  by_contra h
  push Not at h
  obtain ⟨⟨r, hur, hr⟩, s, hvs, hs⟩ := h
  exact hn (hur.trans ((contracted_roots_reachable G fixed hr hs).trans hvs.symm))

theorem components_congr_reachable {G H : SimpleGraph V} (h : G.Reachable = H.Reachable) :
    components G = components H := by
  unfold components component
  rw [h]

omit [Fintype V] in
theorem rootless_union (fixed : V → Prop) (S T : Set V) :
    (∀ r ∈ S ∪ T, ¬ fixed r) ↔ (∀ r ∈ S, ¬ fixed r) ∧ (∀ r ∈ T, ¬ fixed r) := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩
  · rintro ⟨hS, hT⟩ r (hr | hr)
    · exact hS r hr
    · exact hT r hr

/-- Exact ungrounded-component update of an accepted ordinary edge, including
the grounding case. -/
theorem ungrounded_step (G : SimpleGraph V) (fixed : V → Prop) (u v : V)
    (hn : ¬ (contracted G fixed).Reachable u v) :
    let U := component (contracted G fixed) u
    let W := component (contracted G fixed) v
    ungrounded (step fixed G (u,v)) fixed =
      if (∀ r ∈ U, ¬ fixed r) ∧ (∀ r ∈ W, ¬ fixed r)
      then insert (U ∪ W) (((ungrounded G fixed).erase U).erase W)
      else ((ungrounded G fixed).erase U).erase W := by
  dsimp only
  unfold ungrounded
  rw [components_congr_reachable (contracted_step_reachable fixed G (u,v))]
  rw [components_sup_edge _ u v hn]
  simp only [Finset.filter_insert, Finset.filter_erase, rootless_union]

theorem mem_ungrounded (G : SimpleGraph V) (fixed : V → Prop) (a : V) :
    component (contracted G fixed) a ∈ ungrounded G fixed ↔
      ∀ r ∈ component (contracted G fixed) a, ¬ fixed r := by
  have h : component (contracted G fixed) a ∈ components (contracted G fixed) :=
    (mem_components _ _).mpr ⟨a, rfl⟩
  simp only [ungrounded, Finset.mem_filter, h, true_and]

theorem union_not_mem_components (G : SimpleGraph V) (u v : V) (hn : ¬ G.Reachable u v) :
    component G u ∪ component G v ∉ components G := by
  intro h
  obtain ⟨a, ha⟩ := (mem_components _ _).mp h
  have hu : u ∈ component G a := ha.symm ▸ (Or.inl (component_self G u) : u ∈ component G u ∪ component G v)
  have hv : v ∈ component G a := ha.symm ▸ (Or.inr (component_self G v) : v ∈ component G u ∪ component G v)
  exact hn (hu.symm.trans hv)

/-- Each accepted edge decreases the number of actual ungrounded components
by exactly one, whether it merges two free pieces or attaches one to a root. -/
theorem ungrounded_step_card (G : SimpleGraph V) (fixed : V → Prop) (u v : V)
    (hn : ¬ (contracted G fixed).Reachable u v) :
    (ungrounded (step fixed G (u,v)) fixed).card + 1 = (ungrounded G fixed).card := by
  let U := component (contracted G fixed) u
  let W := component (contracted G fixed) v
  have hne : U ≠ W := fun h => hn ((component_eq_iff _ _ _).mp h)
  have hunion : U ∪ W ∉ ((ungrounded G fixed).erase U).erase W := by
    intro h
    have h' := (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
    exact union_not_mem_components _ u v hn (Finset.mem_filter.mp h').1
  rw [ungrounded_step G fixed u v hn]
  change (if (∀ r ∈ U, ¬ fixed r) ∧ (∀ r ∈ W, ¬ fixed r) then
    insert (U ∪ W) (((ungrounded G fixed).erase U).erase W) else
    ((ungrounded G fixed).erase U).erase W).card + 1 = _
  by_cases hU : ∀ r ∈ U, ¬ fixed r
  · have hUm : U ∈ ungrounded G fixed := (mem_ungrounded _ _ _).mpr hU
    have hUc := Finset.card_erase_add_one hUm
    by_cases hW : ∀ r ∈ W, ¬ fixed r
    · have hWm : W ∈ (ungrounded G fixed).erase U :=
        Finset.mem_erase.mpr ⟨hne.symm, (mem_ungrounded _ _ _).mpr hW⟩
      have hWc := Finset.card_erase_add_one hWm
      rw [ite_eq_left ⟨hU, hW⟩, Finset.card_insert_of_notMem hunion]
      omega
    · have hWm : W ∉ (ungrounded G fixed).erase U := fun h =>
        hW ((mem_ungrounded _ _ _).mp (Finset.mem_erase.mp h).2)
      rw [ite_eq_right (fun h => hW h.2), Finset.erase_eq_of_notMem hWm]
      exact hUc
  · have hW := (accepted_has_ungrounded_side G fixed u v hn).resolve_left hU
    have hUm : U ∉ ungrounded G fixed := fun h => hU ((mem_ungrounded _ _ _).mp h)
    rw [ite_eq_right (fun h => hU h.1), Finset.erase_eq_of_notMem hUm]
    exact Finset.card_erase_add_one ((mem_ungrounded _ _ _).mpr hW)

omit [Fintype V] in
theorem component_bot_nonroot (fixed : V → Prop) {a : V} (ha : ¬ fixed a) :
    component (contracted ⊥ fixed) a = {a} := by
  ext b
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => exact Set.mem_singleton _
    | cons hab p =>
      rcases hab with hab | hab
      · exact False.elim hab
      · exact False.elim (ha hab.2.1)
  · intro hb
    have hba : b = a := hb
    subst b
    exact Reachable.rfl

theorem ungrounded_bot (fixed : V → Prop) :
    ungrounded ⊥ fixed = (Finset.univ.filter (fun a => ¬ fixed a)).image (fun a => ({a} : Set V)) := by
  ext S
  simp only [ungrounded, Finset.mem_filter, mem_components, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, ha⟩, hr⟩
    have hna := hr a (ha ▸ component_self (contracted ⊥ fixed) a)
    exact ⟨a, hna, (component_bot_nonroot fixed hna).symm.trans ha⟩
  · rintro ⟨a, hna, rfl⟩
    exact ⟨⟨a, component_bot_nonroot fixed hna⟩, fun r hr => by
      have hra : r = a := hr
      simpa only [hra] using hna⟩

theorem ungrounded_bot_card (fixed : V → Prop) :
    (ungrounded ⊥ fixed).card = Fintype.card {a // ¬ fixed a} := by
  rw [ungrounded_bot, Finset.card_image_of_injective _ Set.singleton_injective]
  exact (Fintype.card_subtype _).symm

/-- The number of accepted candidates in the literal greedy execution. -/
noncomputable def acceptedCount (fixed : V → Prop) : List (V × V) → ℕ
  | [] => 0
  | e :: es => acceptedCount fixed es +
      if (contracted (greedy fixed es) fixed).Reachable e.1 e.2 then 0 else 1

theorem ungrounded_greedy_card (fixed : V → Prop) (es : List (V × V)) :
    (ungrounded (greedy fixed es) fixed).card + acceptedCount fixed es =
      Fintype.card {a // ¬ fixed a} := by
  induction es with
  | nil => simpa only [greedy, acceptedCount, Nat.add_zero] using ungrounded_bot_card fixed
  | cons e es ih =>
    dsimp only [acceptedCount, greedy]
    by_cases he : (contracted (greedy fixed es) fixed).Reachable e.1 e.2
    · simp only [step, ite_eq_left he, Nat.add_zero]
      exact ih
    · rw [ite_eq_right he]
      have h := ungrounded_step_card (greedy fixed es) fixed e.1 e.2 he
      change (ungrounded (step fixed (greedy fixed es) e) fixed).card + 1 = _ at h
      omega

#print axioms components_sup_edge
#print axioms accepted_has_ungrounded_side
#print axioms ungrounded_step_card
#print axioms ungrounded_greedy_card

end ExceptionalTimes.KruskalComponents
