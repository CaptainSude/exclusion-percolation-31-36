import ExceptionalTimes.ForestCounting
import ExceptionalTimes.ProbeProduct

/-! Exact interfaces between literal graph integration and forest counting. -/

open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestBridge

open ForestIntegration ForestCounting

variable {V : Type*} [Fintype V]

noncomputable def adjacencyCount (G : SimpleGraph V) (u v : V) : ℕ :=
  if G.Adj u v then 1 else 0

omit [Fintype V] in
@[simp] theorem adjacencyCount_self (G : SimpleGraph V) (v : V) :
    adjacencyCount G v v = 0 := by simp [adjacencyCount]

omit [Fintype V] in
theorem adjacencyCount_comm (G : SimpleGraph V) (u v : V) :
    adjacencyCount G u v = adjacencyCount G v u := by
  simp only [adjacencyCount, G.adj_comm]

/-- Every edge between listed vertices contributes twice to the adjacency sum;
every edge from a listed vertex to a root contributes once. -/
theorem twice_graphEdgeCount (G : SimpleGraph V) (fixed : V → Prop) (L : List V) :
    2 * graphEdgeCount G fixed L =
      (∑ i : Fin L.length, ∑ j : Fin L.length, adjacencyCount G (L.get i) (L.get j)) +
      2 * ∑ i : Fin L.length, ∑ r : {v // fixed v}, adjacencyCount G (L.get i) r := by
  classical
  induction L with
  | nil => simp [graphEdgeCount]
  | cons v L ih =>
    simp only [graphEdgeCount, Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_sum_type, endpointLabel]
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero,
      List.get_cons_succ', adjacencyCount_self, zero_add, Finset.sum_add_distrib]
    have hsym : (∑ i : Fin L.length, adjacencyCount G (L.get i) v) =
        ∑ i : Fin L.length, adjacencyCount G v (L.get i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact adjacencyCount_comm G _ _
    simp only [adjacencyCount] at ih hsym ⊢
    omega

/-- Listing every non-root gives an actual bijection with the original labels. -/
noncomputable def endpointEquiv (fixed : V → Prop) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) :
    (Fin L.length ⊕ {v // fixed v}) ≃ V :=
  Equiv.ofBijective (endpointLabel fixed L) ⟨
    endpointLabel_injective fixed L hL (fun v hv => (hmem v).mp hv), by
    intro v
    by_cases hv : fixed v
    · exact ⟨.inr ⟨v, hv⟩, rfl⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((hmem v).mpr hv)
      exact ⟨.inl i, hi⟩⟩

omit [Fintype V] in
@[simp] theorem endpointEquiv_apply (fixed : V → Prop) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) (q) :
    endpointEquiv fixed L hL hmem q = endpointLabel fixed L q := rfl

theorem graphEdgeCount_double_sum (G : SimpleGraph V) (fixed : V → Prop)
    (hroots : ∀ u v, fixed u → fixed v → ¬ G.Adj u v)
    (L : List V) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) :
    2 * graphEdgeCount G fixed L = ∑ u : V, ∑ v : V, adjacencyCount G u v := by
  classical
  rw [twice_graphEdgeCount]
  let e := endpointEquiv fixed L hL hmem
  rw [← e.sum_comp (fun u => ∑ v : V, adjacencyCount G u v)]
  simp_rw [← e.sum_comp (fun v => adjacencyCount G _ v)]
  simp only [e, Fintype.sum_sum_type, endpointEquiv_apply,
    endpointLabel, Finset.sum_add_distrib]
  have hz : (∑ r : {v // fixed v}, ∑ s : {v // fixed v},
      adjacencyCount G r s) = 0 := by
    simp [adjacencyCount, hroots _ _ (Subtype.property _) (Subtype.property _)]
  have hsym : (∑ r : {v // fixed v}, ∑ i : Fin L.length,
      adjacencyCount G r (L.get i)) =
      ∑ i : Fin L.length, ∑ r : {v // fixed v}, adjacencyCount G (L.get i) r := by
    rw [Finset.sum_comm]
    simp only [adjacencyCount_comm G]
  omega

theorem twice_forwardEdges {N : ℕ} (G : SimpleGraph (Fin N)) :
    2 * (forwardEdges G).card = ∑ u : Fin N, ∑ v : Fin N, adjacencyCount G u v := by
  classical
  have hp (u v : Fin N) : adjacencyCount G u v =
      (if u < v ∧ G.Adj u v then 1 else 0) +
      (if v < u ∧ G.Adj v u then 1 else 0) := by
    rcases lt_trichotomy u v with h | rfl | h
    · simp [adjacencyCount, h, not_lt.mpr (le_of_lt h)]
    · simp
    · simp [adjacencyCount, h, not_lt.mpr (le_of_lt h), G.adj_comm]
  simp only [forwardEdges, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type]
  simp_rw [hp]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v : Fin N => if v < u ∧ G.Adj v u then 1 else 0)]
  omega

/-- The exponent in leaf integration is exactly the edge count used by the
binomial enumeration, even though the leaf order need not be the numeric order. -/
theorem graphEdgeCount_eq_forwardEdges {N : ℕ} (G : SimpleGraph (Fin N))
    (fixed : Fin N → Prop) (hroot : RootsSeparated G fixed)
    (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v, v ∈ L ↔ ¬ fixed v) :
    graphEdgeCount G fixed L = (forwardEdges G).card := by
  have h := graphEdgeCount_double_sum G fixed (roots_not_adj G fixed hroot) L hL hmem
  have hf := twice_forwardEdges G
  omega

theorem family_sum_le {N k : ℕ} (family : Finset (SimpleGraph (Fin N)))
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hk : ∀ G ∈ family, (forwardEdges G).card ≤ k) :
    (∑ G ∈ family, b (forwardEdges G).card) ≤
      ∑ j ∈ Finset.range (k + 1), ((N ^ 2).choose j : ℝ) * b j := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (fun G hG =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hk G hG))) b]
  apply Finset.sum_le_sum
  intro j hj
  simp only [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hb j)
  exact_mod_cast forest_family_card_le N j
    (family.filter (fun G => (forwardEdges G).card = j))
    (fun G hG => (Finset.mem_filter.mp hG).2)

set_option maxHeartbeats 800000 in
/-- Leaf integration and the edge-family enumeration are applied to the same
graphs. The only analytic premises are one-variable sums and center masses. -/
theorem forest_family_integral_le {N k : ℕ} {X P : Type*} [Fintype X]
    (family : Finset (SimpleGraph (Fin N))) (fixed : Fin N → Prop)
    (L : SimpleGraph (Fin N) → List (Fin N))
    (hgraph : ∀ G ∈ family, G.IsAcyclic ∧ RootsSeparated G fixed)
    (hL : ∀ G ∈ family, (L G).Nodup ∧
      (∀ v, v ∈ L G ↔ ¬ fixed v) ∧ Eliminates G fixed (L G))
    (hlen : ∀ G ∈ family, (L G).length = k)
    (position : X → P) (root : {v // fixed v} → P)
    (μ : ∀ G, Fin (L G).length → X → ℝ)
    (K : ∀ G, Fin (L G).length → X → P → ℝ)
    (M C : ℝ) (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hμ : ∀ G ∈ family, ∀ i a, 0 ≤ μ G i a)
    (hK : ∀ G ∈ family, ∀ i a y, 0 ≤ K G i a y)
    (hM : ∀ G ∈ family, ∀ i, ∑ a, μ G i a ≤ M)
    (hC : ∀ G ∈ family, ∀ i y, ∑ a, μ G i a * K G i a y ≤ C) :
    (∑ G ∈ family, graphIntegral G fixed position root (L G) (μ G) (K G)) ≤
      ∑ j ∈ Finset.range (k + 1), ((N ^ 2).choose j : ℝ) * C ^ j * M ^ (k - j) := by
  classical
  have hencode (G) (hG : G ∈ family) := elimination_encodes G fixed (L G)
    (hL G hG).1 (fun v hv => ((hL G hG).2.1 v).mp hv) (hL G hG).2.2
  have hcount (G) (hG : G ∈ family) := graphEdgeCount_eq_forwardEdges G fixed
    (hgraph G hG).2 (L G) (hL G hG).1 (hL G hG).2.1
  have hk (G) (hG : G ∈ family) : (forwardEdges G).card ≤ k := by
    obtain ⟨F, hF⟩ := hencode G hG
    rw [← hcount G hG, encoded_edgeCount G fixed (L G) F hF, ← hlen G hG]
    exact (Nat.le_add_right F.edgeCount F.freeCount).trans_eq F.counts
  calc
    _ ≤ ∑ G ∈ family, C ^ (forwardEdges G).card * M ^ (k - (forwardEdges G).card) := by
      apply Finset.sum_le_sum
      intro G hG
      obtain ⟨F, hF⟩ := hencode G hG
      have h := graphIntegral_le_count G fixed position root (L G) F hF (μ G) (K G)
        M C (hμ G hG) (hK G hG) hM0 hC0 (hM G hG) (hC G hG)
      simpa only [hcount G hG, hlen G hG] using h
    _ ≤ ∑ j ∈ Finset.range (k + 1), ((N ^ 2).choose j : ℝ) * (C ^ j * M ^ (k-j)) :=
      family_sum_le family (fun j => C ^ j * M ^ (k-j))
        (fun j => mul_nonneg (pow_nonneg hC0 j) (pow_nonneg hM0 (k-j))) hk
    _ = _ := by apply Finset.sum_congr rfl; intro j hj; ring

#print axioms graphEdgeCount_eq_forwardEdges
#print axioms forest_family_integral_le

end ExceptionalTimes.ForestBridge


