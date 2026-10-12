import ExceptionalTimes.WiredBoundary
import ExceptionalTimes.PolygonalWalkPaths
import ExceptionalTimes.NecklacePlaneDisk

/-! Actual planar enclosure implies the graph-cut property used by the
radial reduction. The converse is deliberately not asserted: deleting
cycle vertices can also seal graph pockets outside the drawn polygon. -/

namespace ExceptionalTimes.WiredBoundary

open Set TriangularPlane

theorem bounded_plane_sites_in_box {S : Set (ℝ×ℝ)} (hS : Bornology.IsBounded S) :
    ∃ n : ℕ,∀ v : Site,point v∈S→v∈latticeBox n := by
  obtain ⟨C,hC⟩ := hS.exists_norm_le
  obtain ⟨n,hn⟩ := exists_nat_gt C
  refine ⟨n,?_⟩
  intro v hv
  have h := (hC (point v) hv).trans hn.le
  simp only [Prod.norm_def,Real.norm_eq_abs,point,max_le_iff] at h
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  exact ⟨⟨by exact_mod_cast (abs_le.mp h.1).1,by exact_mod_cast (abs_le.mp h.1).2⟩,
    ⟨by exact_mod_cast (abs_le.mp h.2).1,by exact_mod_cast (abs_le.mp h.2).2⟩⟩

theorem walk_in_complement_component {a b x y : Site}
    (p : triangularGraph.Walk a b) (c : triangularGraph.Walk x y)
    (hdis : ∀ z∈p.support,z∉c.support) :
    point b∈connectedComponentIn (walkTrace c)ᶜ (point a) := by
  have hd := disjoint_supports_disjoint_traces p c hdis
  have hsub : range (walkPath p)⊆(walkTrace c)ᶜ := by
    intro z hz
    rw [walkPath_range] at hz
    exact fun hc => Set.disjoint_left.mp hd hz hc
  have hconnected : IsPreconnected (range (walkPath p)) :=
    isPreconnected_range (walkPath p).continuous
  have ha : point a∈range (walkPath p) := ⟨0,(walkPath p).source⟩
  have hb : point b∈range (walkPath p) := ⟨1,(walkPath p).target⟩
  exact hconnected.subset_connectedComponentIn ha hsub hb

theorem plane_enclosure_separates {a b : Site} (c : triangularGraph.Walk a b)
    (S : Set Site) (hfinite : S.Finite)
    (hinside : ∀ v∈S,Bornology.IsBounded (connectedComponentIn (walkTrace c)ᶜ (point v))) :
    SeparatesFromInfinity S {v | v∈c.support} := by
  classical
  have hbounded : Bornology.IsBounded (⋃ v∈S,connectedComponentIn (walkTrace c)ᶜ (point v)) :=
    (Bornology.isBounded_biUnion hfinite).mpr hinside
  obtain ⟨n,hn⟩ := bounded_plane_sites_in_box hbounded
  refine ⟨latticeBox n∪hfinite.toFinset,?_,?_⟩
  · intro u hu
    exact Finset.mem_union_right _ (hfinite.mem_toFinset.mpr hu)
  · intro u hu v hv p
    by_contra! hnot
    have hc := walk_in_complement_component p c hnot
    have hbox := hn v (Set.mem_iUnion₂.mpr ⟨u,hu,hc⟩)
    exact hv (Finset.mem_union_left _ hbox)

#print axioms plane_enclosure_separates

end ExceptionalTimes.WiredBoundary
