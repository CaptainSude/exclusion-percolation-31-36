import ExceptionalTimes.ForestBridge
import ExceptionalTimes.ForestGeometry

/-! Literal root-contracted greedy edge selection. Virtual edges join all roots;
ordinary edges are accepted only when their endpoints were not already connected
after that contraction. The ordinary output is an acyclic graph with separated
physical roots, and contracting its roots preserves all processed connectivity. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.RootKruskal

open SimpleGraph ForestIntegration

variable {V : Type*}

def rootClique (fixed : V → Prop) : SimpleGraph V where
  Adj u v := u ≠ v ∧ fixed u ∧ fixed v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def contracted (G : SimpleGraph V) (fixed : V → Prop) : SimpleGraph V :=
  G ⊔ rootClique fixed

def Joined (G : SimpleGraph V) (u v a b : V) : Prop :=
  G.Reachable a b ∨ (G.Reachable a u ∧ G.Reachable v b) ∨
    (G.Reachable a v ∧ G.Reachable u b)

theorem Joined.refl (G : SimpleGraph V) (u v a : V) : Joined G u v a a :=
  Or.inl Reachable.rfl

theorem Joined.trans {G : SimpleGraph V} {u v a b c : V}
    (h : Joined G u v a b) (h' : Joined G u v b c) : Joined G u v a c := by
  rcases h with h | ⟨hau, hvb⟩ | ⟨hav, hub⟩
  · rcases h' with h' | ⟨hbu, hvc⟩ | ⟨hbv, huc⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl ⟨h.trans hbu, hvc⟩)
    · exact Or.inr (Or.inr ⟨h.trans hbv, huc⟩)
  · rcases h' with h' | ⟨hbu, hvc⟩ | ⟨hbv, huc⟩
    · exact Or.inr (Or.inl ⟨hau, hvb.trans h'⟩)
    · exact Or.inr (Or.inl ⟨hau, hvc⟩)
    · exact Or.inl (hau.trans huc)
  · rcases h' with h' | ⟨hbu, hvc⟩ | ⟨hbv, huc⟩
    · exact Or.inr (Or.inr ⟨hav, hub.trans h'⟩)
    · exact Or.inl (hav.trans hvc)
    · exact Or.inr (Or.inr ⟨hav, huc⟩)

theorem reachable_sup_edge_iff (G : SimpleGraph V) (u v a b : V) :
    (G ⊔ edge u v).Reachable a b ↔ Joined G u v a b := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Joined.refl G u v _
    | @cons a c b h p ih =>
      apply Joined.trans (b := c) _ ih
      rcases h with h | h
      · exact Or.inl h.reachable
      · rcases (edge_adj u v a c).mp h with ⟨h | h, _⟩
        · rcases h with ⟨rfl, rfl⟩
          exact Or.inr (Or.inl ⟨Reachable.rfl, Reachable.rfl⟩)
        · rcases h with ⟨rfl, rfl⟩
          exact Or.inr (Or.inr ⟨Reachable.rfl, Reachable.rfl⟩)
  · have huv : (G ⊔ edge u v).Reachable u v := by
      by_cases h : u = v
      · subst v; exact Reachable.rfl
      · exact (show (G ⊔ edge u v).Adj u v from Or.inr
          ((edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, h⟩)).reachable
    rintro (h | ⟨hau, hvb⟩ | ⟨hav, hub⟩)
    · exact h.mono le_sup_left
    · exact (hau.mono le_sup_left).trans (huv.trans (hvb.mono le_sup_left))
    · exact (hav.mono le_sup_left).trans (huv.symm.trans (hub.mono le_sup_left))

theorem reachable_sup_edge_of_reachable {G : SimpleGraph V} {u v : V}
    (huv : G.Reachable u v) : (G ⊔ edge u v).Reachable = G.Reachable := by
  funext a b
  apply propext
  rw [reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨hau, hvb⟩ | ⟨hav, hub⟩)
    · exact h
    · exact hau.trans (huv.trans hvb)
    · exact hav.trans (huv.symm.trans hub)
  · exact Or.inl

theorem roots_connected (fixed : V → Prop) (G : SimpleGraph V) {u v : V}
    (hu : fixed u) (hv : fixed v) : (contracted G fixed).Reachable u v := by
  by_cases h : u = v
  · subst v; exact Reachable.rfl
  · exact (show (contracted G fixed).Adj u v from Or.inr ⟨h, hu, hv⟩).reachable

/-- One literal greedy decision; the guard tests the root-contracted graph. -/
noncomputable def step (fixed : V → Prop) (G : SimpleGraph V) (e : V × V) : SimpleGraph V :=
  if (contracted G fixed).Reachable e.1 e.2 then G else G ⊔ edge e.1 e.2

theorem step_isAcyclic (fixed : V → Prop) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (e : V × V) : (step fixed G e).IsAcyclic := by
  unfold step
  split_ifs with h
  · exact hG
  · exact hG.sup_edge_of_not_reachable (fun he => h (he.mono le_sup_left))

theorem step_rootsSeparated (fixed : V → Prop) (G : SimpleGraph V)
    (hG : RootsSeparated G fixed) (e : V × V) : RootsSeparated (step fixed G e) fixed := by
  unfold step
  split_ifs with h
  · exact hG
  · intro a b ha hb hab
    rcases (reachable_sup_edge_iff G e.1 e.2 a b).mp hab with hab | ⟨hau, hvb⟩ | ⟨hav, hub⟩
    · exact hG a b ha hb hab
    · exact False.elim (h ((hau.symm.mono le_sup_left).trans
        ((roots_connected fixed G ha hb).trans (hvb.symm.mono le_sup_left))))
    · exact False.elim (h ((hub.mono le_sup_left).trans
        ((roots_connected fixed G hb ha).trans (hav.mono le_sup_left))))

theorem contracted_step_reachable (fixed : V → Prop) (G : SimpleGraph V) (e : V × V) :
    (contracted (step fixed G e) fixed).Reachable =
      ((contracted G fixed) ⊔ edge e.1 e.2).Reachable := by
  unfold step
  split_ifs with h
  · exact (reachable_sup_edge_of_reachable h).symm
  · congr 1
    unfold contracted
    ac_rfl

noncomputable def greedy (fixed : V → Prop) : List (V × V) → SimpleGraph V
  | [] => ⊥
  | e :: es => step fixed (greedy fixed es) e

def processed : List (V × V) → SimpleGraph V
  | [] => ⊥
  | e :: es => processed es ⊔ edge e.1 e.2

theorem greedy_isAcyclic (fixed : V → Prop) (es : List (V × V)) :
    (greedy fixed es).IsAcyclic := by
  induction es with
  | nil => exact isAcyclic_bot
  | cons e es ih => exact step_isAcyclic fixed _ ih e

theorem greedy_rootsSeparated (fixed : V → Prop) (es : List (V × V)) :
    RootsSeparated (greedy fixed es) fixed := by
  induction es with
  | nil => intro a b ha hb hab; simpa [greedy] using hab
  | cons e es ih => exact step_rootsSeparated fixed _ ih e

theorem contracted_greedy_reachable (fixed : V → Prop) (es : List (V × V)) :
    (contracted (greedy fixed es) fixed).Reachable =
      (contracted (processed es) fixed).Reachable := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [greedy, contracted_step_reachable]
    have he : contracted (processed (e::es)) fixed =
        contracted (processed es) fixed ⊔ edge e.1 e.2 := by
      simp only [processed, contracted]
      ac_rfl
    rw [he]
    funext a b
    apply propext
    simp only [reachable_sup_edge_iff, Joined, ih]

theorem processed_adj (es : List (V × V)) (a b : V) :
    (processed es).Adj a b ↔ ∃ e ∈ es, (edge e.1 e.2).Adj a b := by
  induction es with
  | nil => simp [processed]
  | cons e es ih =>
    simp only [processed, sup_adj, ih, List.mem_cons]
    constructor
    · rintro (⟨f, hf, hab⟩ | hab)
      · exact ⟨f, Or.inr hf, hab⟩
      · exact ⟨e, Or.inl rfl, hab⟩
    · rintro ⟨f, h | h, hab⟩
      · subst f; exact Or.inr hab
      · exact Or.inl ⟨f, h, hab⟩

theorem greedy_edgeCount_le (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hroots : Fintype.card {v // fixed v} = J) (es : List (Fin (k+J) × Fin (k+J))) :
    (ForestCounting.forwardEdges (greedy fixed es)).card ≤ k := by
  obtain ⟨L, F, hL, hmem, hF⟩ := exists_graph_encoding (greedy fixed es)
    (greedy_isAcyclic fixed es) fixed (greedy_rootsSeparated fixed es)
  have hlen := Fintype.card_congr (ForestBridge.endpointEquiv fixed L hL hmem)
  simp only [Fintype.card_sum, Fintype.card_fin, hroots] at hlen
  rw [← ForestBridge.graphEdgeCount_eq_forwardEdges _ _ (greedy_rootsSeparated fixed es) L hL hmem,
    encoded_edgeCount _ _ L F hF]
  have hh := F.counts
  omega

section Thresholds

variable [Fintype V] {X : Type*} [PseudoMetricSpace X]

def threshold (position : V → X) (cutoff t : ℝ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ max (dist (position u) (position v)) cutoff < t
  symm := ⟨fun u v h => ⟨h.1.symm, by simpa only [_root_.dist_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Candidate edges below a strict threshold; a deterministic finite ordering
also resolves ties in the greedy algorithm. -/
noncomputable def edgesBelow (position : V → X) (cutoff t : ℝ) : List (V × V) :=
  Finset.univ.toList.filter (fun e => max (dist (position e.1) (position e.2)) cutoff < t)

theorem processed_edgesBelow (position : V → X) (cutoff t : ℝ) :
    processed (edgesBelow position cutoff t) = threshold position cutoff t := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  rw [processed_adj]
  constructor
  · rintro ⟨⟨u,v⟩, hmem, hab⟩
    have hlen := of_decide_eq_true (List.mem_filter.mp hmem).2
    rcases (edge_adj u v a b).mp hab with ⟨h | h, hne⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨hne, hlen⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨hne, by simpa only [Prod.fst, Prod.snd, _root_.dist_comm] using hlen⟩
  · rintro ⟨hne, hlen⟩
    exact ⟨(a,b), by simpa only [edgesBelow, List.mem_filter, Finset.mem_toList,
      Finset.mem_univ, true_and, decide_eq_true_eq] using hlen,
      (edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩, hne⟩⟩

/-- Accepted edges have exactly the root-contracted threshold components.
This is an identity of actual graph-walk reachability relations. -/
theorem greedy_threshold_reachable (fixed : V → Prop) (position : V → X) (cutoff t : ℝ) :
    (contracted (greedy fixed (edgesBelow position cutoff t)) fixed).Reachable =
      (contracted (threshold position cutoff t) fixed).Reachable := by
  rw [contracted_greedy_reachable, processed_edgesBelow]

omit [Fintype V] in
theorem threshold_mono (position : V → X) (cutoff : ℝ) {s t : ℝ} (hst : s ≤ t) :
    threshold position cutoff s ≤ threshold position cutoff t := by
  intro u v huv
  exact ⟨huv.1, huv.2.trans_le hst⟩

/-- The root-contracted component of an anchor in the literal threshold graph. -/
def cluster (fixed : V → Prop) (position : V → X) (cutoff t : ℝ) (a : V) : Set V :=
  {v | (contracted (threshold position cutoff t) fixed).Reachable a v}

omit [Fintype V] in
theorem cluster_self (fixed : V → Prop) (position : V → X) (cutoff t : ℝ) (a : V) :
    a ∈ cluster fixed position cutoff t a := Reachable.rfl

omit [Fintype V] in
/-- Threshold components are nested or disjoint, with roots already contracted. -/
theorem clusters_nested_of_overlap (fixed : V → Prop) (position : V → X) (cutoff : ℝ)
    {s t : ℝ} (hst : s ≤ t) {a b z : V}
    (hza : z ∈ cluster fixed position cutoff s a)
    (hzb : z ∈ cluster fixed position cutoff t b) :
    cluster fixed position cutoff s a ⊆ cluster fixed position cutoff t b := by
  intro x hx
  have hm : contracted (threshold position cutoff s) fixed ≤
      contracted (threshold position cutoff t) fixed := sup_le_sup_right (threshold_mono position cutoff hst) _
  exact hzb.trans ((hza.mono hm).symm.trans (hx.mono hm))

omit [Fintype V] in
theorem cluster_external_separation (fixed : V → Prop) (position : V → X) (cutoff t : ℝ)
    {a x y : V} (hx : x ∈ cluster fixed position cutoff t a)
    (hy : y ∉ cluster fixed position cutoff t a) :
    t ≤ max (dist (position x) (position y)) cutoff := by
  by_contra h
  have hxy : x ≠ y := by intro he; exact hy (he ▸ hx)
  have hadj : (contracted (threshold position cutoff t) fixed).Adj x y :=
    Or.inl ⟨hxy, lt_of_not_ge h⟩
  exact hy (hx.trans hadj.reachable)

omit [Fintype V] in
/-- For a positive life above the cutoff, clipping can be removed. -/
theorem cluster_external_distance (fixed : V → Prop) (position : V → X) {cutoff t : ℝ}
    (ht : cutoff < t) {a x y : V}
    (hx : x ∈ cluster fixed position cutoff t a)
    (hy : y ∉ cluster fixed position cutoff t a) :
    t ≤ dist (position x) (position y) := by
  have h := cluster_external_separation fixed position cutoff t hx hy
  exact (le_max_iff.mp h).resolve_right (not_le.mpr ht)

end Thresholds

#print axioms greedy_isAcyclic
#print axioms greedy_rootsSeparated
#print axioms contracted_greedy_reachable
#print axioms greedy_edgeCount_le
#print axioms greedy_threshold_reachable
#print axioms clusters_nested_of_overlap
#print axioms cluster_external_distance

end ExceptionalTimes.RootKruskal


