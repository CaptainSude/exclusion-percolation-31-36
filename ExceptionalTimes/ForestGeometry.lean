import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Verified metric ingredient of the forest diameter charge

This module proves the spanning-length inequality used in the forest argument,
including clipped edge lengths. Reachability is the actual graph-walk notion.
No planar arm estimate, Kruskal life invariant, or forest-integral conclusion is
assumed or asserted here.
-/

namespace ExceptionalTimes.ForestGeometry

open scoped BigOperators

variable {V X : Type*} [PseudoMetricSpace X]

/-- Physical edge length with a lower microscopic cutoff. -/
noncomputable def clippedEdgeLength (position : V → X) (cutoff : ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => max (dist (position u) (position v)) cutoff,
    fun u v => by dsimp; rw [dist_comm]⟩

@[simp]
theorem clippedEdgeLength_mk (position : V → X) (cutoff : ℝ) (u v : V) :
    clippedEdgeLength position cutoff s(u, v) =
      max (dist (position u) (position v)) cutoff := rfl

theorem clippedEdgeLength_nonneg (position : V → X) (cutoff : ℝ) (e : Sym2 V) :
    0 ≤ clippedEdgeLength position cutoff e := by
  induction e using Sym2.inductionOn with
  | _ u v => exact (dist_nonneg).trans (le_max_left _ _)

/-- Triangle inequality along an actual graph walk, with every traversal counted. -/
theorem dist_le_walk_edge_sum (position : V → X) (cutoff : ℝ)
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    dist (position u) (position v) ≤
      (p.edges.map (clippedEdgeLength position cutoff)).sum := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
      clippedEdgeLength_mk]
    exact (dist_triangle (position u) (position v) (position w)).trans
      (add_le_add (le_max_left _ _) ih)

/-- A trail uses each edge once, so its distance is bounded by the total length
of any finite recorded edge set containing its traversed edges. -/
theorem dist_le_recorded_edge_sum (position : V → X) (cutoff : ℝ)
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsTrail)
    (recorded : Finset (Sym2 V)) (hrecorded : ∀ e ∈ p.edges, e ∈ recorded) :
    dist (position u) (position v) ≤
      ∑ e ∈ recorded, clippedEdgeLength position cutoff e := by
  classical
  refine (dist_le_walk_edge_sum position cutoff p).trans ?_
  rw [← List.sum_toFinset _ hp.edges_nodup]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact hrecorded e (List.mem_toFinset.mp he)
  · intro e _ _
    exact clippedEdgeLength_nonneg position cutoff e

/-- The spanning-length diameter bound: connecting vertices by the recorded
graph suffices. The graph need not be a tree; taking a simple path removes every
repeated traversal before charging the finite recorded edges. -/
theorem reachable_dist_le_recorded_edge_sum (position : V → X) (cutoff : ℝ)
    {G : SimpleGraph V} (recorded : Finset (Sym2 V))
    (hrecorded : ∀ e ∈ G.edgeSet, e ∈ recorded)
    {u v : V} (h : G.Reachable u v) :
    dist (position u) (position v) ≤
      ∑ e ∈ recorded, clippedEdgeLength position cutoff e := by
  obtain ⟨p, hp⟩ := h.exists_isPath
  exact dist_le_recorded_edge_sum position cutoff p hp.isTrail recorded
    (fun e he => hrecorded e (p.edges_subset_edgeSet he))

#print axioms reachable_dist_le_recorded_edge_sum

end ExceptionalTimes.ForestGeometry
