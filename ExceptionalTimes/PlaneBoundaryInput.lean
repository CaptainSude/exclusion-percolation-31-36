import ExceptionalTimes.PlaneCircuitSeparation

/-! The full planar meaning of the finite-cluster surrounding-circuit
input. Source: Grimmett, Probability on Graphs, author's revision of
5 July 2012, section 5.5, printed pp. 99--100, the external-boundary
cycle paragraph and the subsequent bounded-complement convention.

The already used graph-cut input records only one consequence of
surrounding. Here the geometric enclosure is explicit. No pivotal-arm,
annular probability, ordering, or sewing assertion is contained in it.
The implication to the old graph-cut interface is proved below.

This is an explicit imported proposition, not an axiom or a proved theorem.
The source external-boundary statement is read in its enclosing sense,
as in its referenced Figure 3.1. Axial coordinates give an affine drawing
of the same triangular lattice; connected components and boundedness
have the same meaning under this invertible change of coordinates.
-/

namespace ExceptionalTimes.WiredBoundary

open TriangularPlane

def PlaneClusterBoundaryCircuit : Prop :=
  ∀ (η : Configuration) (o : Site),η o=true→(BlackCluster η o).Finite→
    ∃ v : Site,∃ c : triangularGraph.Walk v v,c.IsCycle ∧
      (∀ z∈c.support,z∈Necklace.externalBoundary triangularGraph (BlackCluster η o)) ∧
      (∀ z∈BlackCluster η o,
        Bornology.IsBounded (connectedComponentIn (walkTrace c)ᶜ (point z)))

theorem PlaneClusterBoundaryCircuit.graph_cut (h : PlaneClusterBoundaryCircuit) :
    FiniteClusterBoundaryCircuit := by
  intro η o ho hfinite
  obtain ⟨v,c,hc,hboundary,hinside⟩ := h η o ho hfinite
  exact ⟨v,c,hc,hboundary,plane_enclosure_separates c _ hfinite hinside⟩

#print axioms PlaneClusterBoundaryCircuit.graph_cut

end ExceptionalTimes.WiredBoundary
