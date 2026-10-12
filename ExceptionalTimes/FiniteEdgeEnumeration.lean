import ExceptionalTimes.FiniteMatchingComparison

open scoped Classical

namespace ExceptionalTimes.FiniteEdgeEnumeration

open FiniteClockBridge

noncomputable def vertices (F : Finset (Sym2 Site)) : Finset Site :=
  F.biUnion (fun e => {e.out.1, e.out.2})

theorem left_mem_vertices {F : Finset (Sym2 Site)} (e : F) : e.val.out.1 ∈ vertices F :=
  Finset.mem_biUnion.mpr ⟨e.val, e.property, by simp⟩

theorem right_mem_vertices {F : Finset (Sym2 Site)} (e : F) : e.val.out.2 ∈ vertices F :=
  Finset.mem_biUnion.mpr ⟨e.val, e.property, by simp⟩

/-- Every retained unordered edge is enumerated once, including zero-rate
or diagonal indices. A diagonal coordinate swap is automatically identity. -/
noncomputable def enumerate (F : Finset (Sym2 Site)) (V : Finset Site)
    (hV : vertices F ⊆ V) (e : F) : V × V :=
  (⟨e.val.out.1, hV (left_mem_vertices e)⟩, ⟨e.val.out.2, hV (right_mem_vertices e)⟩)

theorem enumerate_edgePair (F : Finset (Sym2 Site)) (V : Finset Site)
    (hV : vertices F ⊆ V) (e : F) : edgePair V (enumerate F V hV) e = e.val := by
  change s(e.val.out.1, e.val.out.2) = e.val
  exact e.val.out_eq

theorem enumerate_injective (F : Finset (Sym2 Site)) (V : Finset Site)
    (hV : vertices F ⊆ V) : Function.Injective (edgePair V (enumerate F V hV)) := by
  intro e f he
  apply Subtype.ext
  simpa only [enumerate_edgePair] using he

theorem enumerate_retainedEdges (F : Finset (Sym2 Site)) (V : Finset Site)
    (hV : vertices F ⊆ V) : retainedEdges V (enumerate F V hV) = F := by
  ext e
  simp only [retainedEdges, Finset.mem_image, Finset.mem_univ, true_and, enumerate_edgePair]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro he
    exact ⟨⟨e, he⟩, rfl⟩

#print axioms enumerate_retainedEdges

end ExceptionalTimes.FiniteEdgeEnumeration
