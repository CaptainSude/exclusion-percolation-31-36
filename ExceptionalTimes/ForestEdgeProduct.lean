import ExceptionalTimes.ForestArmRadial
import ExceptionalTimes.ForestBridge

/-! Reindexing literal unordered graph-edge products into the leaf order used
by forest integration. No bound or independence statement is an input. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestEdgeProduct

open ForestIntegration ForestCounting ForestBridge

variable {V : Type*} [Fintype V]

noncomputable def edgeFactor (G : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) : ℝ :=
  if G.Adj u v then w s(u,v) else 1

omit [Fintype V] in
@[simp] theorem edgeFactor_self (G : SimpleGraph V) (w : Sym2 V → ℝ) (v : V) :
    edgeFactor G w v v = 1 := by simp [edgeFactor]

omit [Fintype V] in
theorem edgeFactor_comm (G : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) :
    edgeFactor G w u v = edgeFactor G w v u := by
  simp only [edgeFactor, G.adj_comm, Sym2.eq_swap]

noncomputable def orderedProduct (G : SimpleGraph V) (fixed : V → Prop) (w : Sym2 V → ℝ) : List V → ℝ
  | [] => 1
  | v :: L => (∏ q : Fin L.length ⊕ {r // fixed r}, edgeFactor G w v (endpointLabel fixed L q)) *
      orderedProduct G fixed w L

theorem orderedProduct_nonneg (G : SimpleGraph V) (fixed : V → Prop) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (L : List V) : 0 ≤ orderedProduct G fixed w L := by
  induction L with
  | nil => simp [orderedProduct]
  | cons v L ih =>
    apply mul_nonneg _ ih
    apply Finset.prod_nonneg
    intro q _
    unfold edgeFactor
    split_ifs
    · exact hw _
    · norm_num

theorem orderedProduct_sq (G : SimpleGraph V) (fixed : V → Prop) (w : Sym2 V → ℝ) (L : List V) :
    (orderedProduct G fixed w L)^2 =
      (∏ i : Fin L.length, ∏ j : Fin L.length, edgeFactor G w (L.get i) (L.get j)) *
        (∏ i : Fin L.length, ∏ r : {v // fixed v}, edgeFactor G w (L.get i) r)^2 := by
  induction L with
  | nil => simp [orderedProduct]
  | cons v L ih =>
    simp only [orderedProduct, Fintype.prod_sum_type, endpointLabel]
    simp only [List.length_cons, Fin.prod_univ_succ, List.get_cons_zero,
      List.get_cons_succ', edgeFactor_self, one_mul, Finset.prod_mul_distrib]
    have hsym : (∏ i : Fin L.length, edgeFactor G w (L.get i) v) =
        ∏ i : Fin L.length, edgeFactor G w v (L.get i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact edgeFactor_comm G w _ _
    rw [hsym]
    calc
      _ = ((∏ i : Fin L.length, edgeFactor G w v (L.get i)) *
          ∏ r : {v // fixed v}, edgeFactor G w v r)^2 * (orderedProduct G fixed w L)^2 := by ring
      _ = _ := by rw [ih]; ring

theorem orderedProduct_sq_all (G : SimpleGraph V) (fixed : V → Prop) (w : Sym2 V → ℝ)
    (hroots : ∀ u v, fixed u → fixed v → ¬ G.Adj u v)
    (L : List V) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) :
    (orderedProduct G fixed w L)^2 = ∏ u : V, ∏ v : V, edgeFactor G w u v := by
  rw [orderedProduct_sq]
  let e := endpointEquiv fixed L hL hmem
  rw [← e.prod_comp (fun u => ∏ v : V, edgeFactor G w u v)]
  simp_rw [← e.prod_comp (fun v => edgeFactor G w _ v)]
  simp only [e, Fintype.prod_sum_type, endpointEquiv_apply,
    endpointLabel, Finset.prod_mul_distrib]
  have hz : (∏ r : {v // fixed v}, ∏ s : {v // fixed v}, edgeFactor G w r s) = 1 := by
    simp [edgeFactor, hroots _ _ (Subtype.property _) (Subtype.property _)]
  have hsym : (∏ r : {v // fixed v}, ∏ i : Fin L.length, edgeFactor G w r (L.get i)) =
      ∏ i : Fin L.length, ∏ r : {v // fixed v}, edgeFactor G w (L.get i) r := by
    rw [Finset.prod_comm]
    simp only [edgeFactor_comm G w]
  rw [hz, hsym]
  ring

theorem prod_edgeFinset_eq_forward {N : ℕ} (G : SimpleGraph (Fin N)) (w : Sym2 (Fin N) → ℝ) :
    (∏ e ∈ G.edgeFinset, w e) = ∏ e ∈ forwardEdges G, w s(e.1,e.2) := by
  symm
  apply Finset.prod_bij (fun e _ => s(e.1,e.2))
  · intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp he).2.2
  · intro e he f hf h
    obtain ⟨u,v⟩ := e
    obtain ⟨x,y⟩ := f
    have huv := (Finset.mem_filter.mp he).2.1
    have hxy := (Finset.mem_filter.mp hf).2.1
    rcases Sym2.eq_iff.mp h with h | h
    · exact Prod.ext h.1 h.2
    · exfalso
      rcases h with ⟨rfl,rfl⟩
      exact (lt_asymm huv hxy)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases lt_or_gt_of_ne hadj.ne with huv | hvu
      · exact ⟨(u,v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, hadj⟩, rfl⟩
      · exact ⟨(v,u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu, hadj.symm⟩, Sym2.eq_swap⟩
  · intro _ _
    rfl

theorem edgeProduct_sq {N : ℕ} (G : SimpleGraph (Fin N)) (w : Sym2 (Fin N) → ℝ) :
    (∏ e ∈ G.edgeFinset, w e)^2 = ∏ u : Fin N, ∏ v : Fin N, edgeFactor G w u v := by
  have hf (u v : Fin N) : edgeFactor G w u v =
      (if u < v then edgeFactor G w u v else 1) *
        (if v < u then edgeFactor G w u v else 1) := by
    rcases lt_trichotomy u v with h | rfl | h
    · simp [h, not_lt_of_ge (le_of_lt h)]
    · simp
    · simp [h, not_lt_of_ge (le_of_lt h)]
  have hhalf : (∏ u : Fin N, ∏ v : Fin N, if u < v then edgeFactor G w u v else 1) =
      ∏ e ∈ forwardEdges G, w s(e.1,e.2) := by
    simp only [forwardEdges, Finset.prod_filter, Fintype.prod_prod_type, edgeFactor]
    apply Finset.prod_congr rfl
    intro u _
    apply Finset.prod_congr rfl
    intro v _
    by_cases huv : u < v <;> by_cases hadj : G.Adj u v <;> simp [huv, hadj]
  have hother : (∏ u : Fin N, ∏ v : Fin N, if v < u then edgeFactor G w u v else 1) =
      ∏ u : Fin N, ∏ v : Fin N, if u < v then edgeFactor G w u v else 1 := by
    rw [Finset.prod_comm]
    simp only [edgeFactor_comm G w]
  conv_rhs => arg 2; ext u; arg 2; ext v; rw [hf]
  simp only [Finset.prod_mul_distrib]
  rw [hother, hhalf, prod_edgeFinset_eq_forward]
  ring

theorem orderedProduct_eq_edges {N : ℕ} (G : SimpleGraph (Fin N)) (fixed : Fin N → Prop)
    (w : Sym2 (Fin N) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hroots : ∀ u v, fixed u → fixed v → ¬ G.Adj u v)
    (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) :
    orderedProduct G fixed w L = ∏ e ∈ G.edgeFinset, w e := by
  have h1 := orderedProduct_sq_all G fixed w hroots L hL hmem
  have h2 := edgeProduct_sq G w
  have hp := orderedProduct_nonneg G fixed w hw L
  have hq : 0 ≤ ∏ e ∈ G.edgeFinset, w e := Finset.prod_nonneg (fun e _ => hw e)
  nlinarith

section Spatial

variable {A P : Type*}

noncomputable def spatialWeight (φ : V → P) (κ : P → P → ℝ)
    (hsym : ∀ a b, κ a b = κ b a) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => κ (φ u) (φ v), fun u v => hsym (φ u) (φ v)⟩

theorem graphProduct_spatial (G : SimpleGraph V) (fixed : V → Prop) (φ : V → P)
    (position : A → P) (root : {v // fixed v} → P) (L : List V)
    (κ : P → P → ℝ) (hsym : ∀ a b, κ a b = κ b a) (x : Fin L.length → A)
    (hx : ∀ i, position (x i) = φ (L.get i)) (hr : ∀ r, root r = φ r) :
    graphProduct G fixed position root L (fun _ a b => κ (position a) b) x =
      orderedProduct G fixed (spatialWeight φ κ hsym) L := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [graphProduct, orderedProduct]
    apply congrArg₂ (fun a b : ℝ => a*b)
    · apply Finset.prod_congr rfl
      intro q _
      unfold edgeFactor
      split_ifs
      · cases q with
        | inl j =>
          change κ (position (x 0)) (position (x j.succ)) = κ (φ v) (φ (L.get j))
          simpa only [List.get_cons_zero, List.get_cons_succ'] using congrArg₂ κ (hx 0) (hx j.succ)
        | inr r =>
          change κ (position (x 0)) (root r) = κ (φ v) (φ r)
          simpa only [List.get_cons_zero] using congrArg₂ κ (hx 0) (hr r)
      · rfl
    · apply ih (fun j => x j.succ)
      intro i
      simpa only [List.get_cons_succ'] using hx i.succ

/-- The position of every original label is reconstructed from the actual
variable assignment and the fixed-root coordinates. -/
noncomputable def configuredPosition (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) (x : Fin L.length → A) (v : V) : P :=
  endpointPosition fixed position root x ((endpointEquiv fixed L hL hmem).symm v)

omit [Fintype V] in
theorem configuredPosition_get (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) (x : Fin L.length → A) (i : Fin L.length) :
    configuredPosition fixed position root L hL hmem x (L.get i) = position (x i) := by
  have h := (endpointEquiv fixed L hL hmem).symm_apply_apply (.inl i)
  change (endpointEquiv fixed L hL hmem).symm (L.get i) = .inl i at h
  unfold configuredPosition
  rw [h]
  rfl

omit [Fintype V] in
theorem configuredPosition_root (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) (x : Fin L.length → A) (r : {v // fixed v}) :
    configuredPosition fixed position root L hL hmem x r = root r := by
  have h := (endpointEquiv fixed L hL hmem).symm_apply_apply (.inr r)
  change (endpointEquiv fixed L hL hmem).symm r = .inr r at h
  unfold configuredPosition
  rw [h]
  rfl

/-- Exact dictionary between the graph product integrated by leaf elimination
and the ordinary unordered edge product under the same position assignment. -/
theorem graphProduct_eq_edges {N : ℕ} (G : SimpleGraph (Fin N)) (fixed : Fin N → Prop)
    (position : A → P) (root : {v // fixed v} → P)
    (hroots : ∀ u v, fixed u → fixed v → ¬ G.Adj u v)
    (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v)
    (κ : P → P → ℝ) (hsym : ∀ a b, κ a b = κ b a) (hκ : ∀ a b, 0 ≤ κ a b)
    (x : Fin L.length → A) :
    graphProduct G fixed position root L (fun _ a b => κ (position a) b) x =
      ∏ e ∈ G.edgeFinset,
        spatialWeight (configuredPosition fixed position root L hL hmem x) κ hsym e := by
  rw [graphProduct_spatial G fixed (configuredPosition fixed position root L hL hmem x)
    position root L κ hsym x
    (fun i => (configuredPosition_get fixed position root L hL hmem x i).symm)
    (fun r => (configuredPosition_root fixed position root L hL hmem x r).symm)]
  apply orderedProduct_eq_edges G fixed _ _ hroots L hL hmem
  intro e
  induction e using Sym2.inductionOn with
  | _ u v => exact hκ _ _

end Spatial

#print axioms orderedProduct_eq_edges
#print axioms graphProduct_eq_edges

end ExceptionalTimes.ForestEdgeProduct
