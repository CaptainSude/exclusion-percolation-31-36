import ExceptionalTimes.FiniteClosedPaths

/-! A connected set cannot change between a finite family of closed sets
without meeting two of them. Used to label polygon edges by marked sides. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

theorem preconnected_finite_closed_partition {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (F : ι → Set X) (hclosed : ∀ i ∈ s, IsClosed (F i))
    {K : Set X} (hK : IsPreconnected K) (hne : K.Nonempty)
    (hcover : K ⊆ ⋃ i ∈ s, F i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i≠j → ∀ x ∈ K, x ∈ F i → x ∉ F j) :
    ∃ i ∈ s, K ⊆ F i := by
  classical
  obtain ⟨a,ha⟩ := hne
  obtain ⟨i,hi,hai⟩ := mem_iUnion₂.mp (hcover ha)
  refine ⟨i,hi,?_⟩
  let R := ⋃ j ∈ s.filter (fun j => j≠i), F j
  have hR : IsClosed R := isClosed_biUnion_finset
    (fun j hj => hclosed j (Finset.mem_filter.mp hj).1)
  have hcov : K ⊆ F i ∪ R := by
    intro x hx
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (hcover hx)
    by_cases hji : j=i
    · exact Or.inl (hji ▸ hxj)
    · exact Or.inr (mem_iUnion₂_of_mem (Finset.mem_filter.mpr ⟨hj,hji⟩) hxj)
  intro b hb
  by_contra hn
  have hbR : b ∈ R := (hcov hb).resolve_left hn
  obtain ⟨x,hx,hxi,hxR⟩ := isPreconnected_closed_iff.mp hK (F i) R (hclosed i hi) hR hcov
    ⟨a,ha,hai⟩ ⟨b,hb,hbR⟩
  obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hxR
  have hj' := Finset.mem_filter.mp hj
  exact hdis j hj'.1 i hi hj'.2 x hx hxj hxi

#print axioms preconnected_finite_closed_partition

end ExceptionalTimes.PairSquareSewing
