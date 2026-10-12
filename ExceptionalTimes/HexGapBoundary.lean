import ExceptionalTimes.CardinalTrackGeometry
import ExceptionalTimes.HexCycleTrace

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open Annulus

theorem path_start_not_in_tail {u v : Site} {p : triangularGraph.Walk u v}
    (hp : p.IsPath) : u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [←p.cons_tail_support] at h
  exact (List.nodup_cons.mp h).1

theorem path_append_of_unique_contact {u v w : Site}
    {p : triangularGraph.Walk u v} {q : triangularGraph.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hcontact : ∀ z ∈ p.support, z ∈ q.support → z=v) : (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_append,List.nodup_append']
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  apply List.disjoint_left.mpr
  intro z hz hzq
  have hqz : z ∈ q.support := List.mem_of_mem_tail hzq
  have he := hcontact z hz hqz
  exact path_start_not_in_tail hq (he ▸ hzq)

/-- Two proper disjoint radial paths and simple paths on the two exact
cut levels form an actual simple graph cycle. This statement establishes
the boundary; it does not yet identify which component is the intended
gap between adjacent arms. -/
theorem proper_paths_cut_boundary_cycle (f : Site → ℤ) (r R : ℤ) (hrR : r < R)
    {x y X Y : Site} (p : triangularGraph.Walk x y) (q : triangularGraph.Walk X Y)
    (hp : p.IsPath) (hq : q.IsPath) (hdis : List.Disjoint p.support q.support)
    (hx : f x=r) (hy : f y=R) (hX : f X=r) (hY : f Y=R)
    (hpr : ∀ z ∈ p.support, f z=r → z=x) (hpR : ∀ z ∈ p.support, f z=R → z=y)
    (hqr : ∀ z ∈ q.support, f z=r → z=X) (hqR : ∀ z ∈ q.support, f z=R → z=Y)
    (outer : triangularGraph.Walk y Y) (inner : triangularGraph.Walk X x)
    (ho : outer.IsPath) (hi : inner.IsPath)
    (hout : ∀ z ∈ outer.support, f z=R) (hin : ∀ z ∈ inner.support, f z=r) :
    (((p.append outer).append q.reverse).append inner).IsCycle := by
  have hpo : (p.append outer).IsPath :=
    path_append_of_unique_contact hp ho (fun z hz hzout => hpR z hz (hout z hzout))
  have hop : ((p.append outer).append q.reverse).IsPath := by
    apply path_append_of_unique_contact hpo hq.reverse
    intro z hz hzq
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hzq
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact (List.disjoint_left.mp hdis hz hzq).elim
    · exact hqR z hzq (hout z hz)
  apply hop.isCycle_append hi
  · apply List.disjoint_left.mpr
    intro z hz hzi
    have hz' := List.mem_of_mem_tail hz
    have hzi' := List.mem_of_mem_tail hzi
    simp only [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz'
    rcases hz' with (hzp | hzo) | hzq
    · exact path_start_not_in_tail hop (hpr z hzp (hin z hzi') ▸ hz)
    · have := hout z hzo
      have := hin z hzi'
      omega
    · exact path_start_not_in_tail hi (hqr z hzq (hin z hzi') ▸ hzi)
  · left
    have hpL : 0 < p.length := by
      apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
      intro h
      have he := h.eq
      rw [he] at hx
      omega
    have hoL : 0 < outer.length := by
      apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
      intro h
      have he := h.eq
      exact List.disjoint_left.mp hdis p.end_mem_support (he ▸ q.end_mem_support)
    simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse]
    omega

/-- The exact hex-cut cycle supplies a simple boundary arc between any
two of its lattice vertices; all arc sites remain on the same cut. -/
theorem hex_boundary_path (n : ℕ) {u v : Site}
    (hu : hexRadius u=(n+1:ℕ)) (hv : hexRadius v=(n+1:ℕ)) :
    ∃ p : triangularGraph.Walk u v, p.IsPath ∧
      ∀ z ∈ p.support, hexRadius z=(n+1:ℕ) := by
  have huC : u ∈ (hexCycle n).support := by
    have h := hexCycle_support n
    exact (Set.ext_iff.mp h u).mpr hu
  have hvC : v ∈ (hexCycle n).support := by
    have h := hexCycle_support n
    exact (Set.ext_iff.mp h v).mpr hv
  obtain ⟨q,hq⟩ := walk_between_support (hexCycle n) huC hvC
  refine ⟨q.toPath.val,q.toPath.property,?_⟩
  intro z hz
  exact (Set.ext_iff.mp (hexCycle_support n) z).mp (hq z (q.support_toPath_subset_support hz))

theorem level_path_trace_on_hex_cut (n : ℕ) {u v : Site} (p : triangularGraph.Walk u v)
    (hp : ∀ z ∈ p.support, hexRadius z=(n+1:ℕ)) :
    TriangularPlane.walkTrace p ⊆ {q | hexGauge q=(n+1:ℕ)} := by
  intro q hq
  rcases TriangularPlane.walkTrace_point_or_edge p hq with ⟨z,hz,rfl⟩ |
    ⟨a,ha,b,hb,hadj,t,ht0,ht1,rfl⟩
  · change hexGauge (TriangularPlane.point z)=_
    rw [hexGauge_point,hp z hz]
    norm_cast
  · exact boundary_edge_hexGauge (by omega) (hp a ha) (hp b hb) hadj ht0 ht1

/-- A concrete boundary cycle exists for any two proper disjoint paths
between the exact inner and outer hex cuts. Both joining arcs have their
whole Euclidean traces on those cut boundaries. Selecting the adjacent
arcs and proving the resulting four disks partition the annulus remain
distinct topological obligations. -/
theorem hex_paths_have_cut_boundary_cycle (n N : ℕ) (hnN : n < N)
    {x y X Y : Site} (p : triangularGraph.Walk x y) (q : triangularGraph.Walk X Y)
    (hp : p.IsPath) (hq : q.IsPath) (hdis : List.Disjoint p.support q.support)
    (hx : hexRadius x=(n+1:ℕ)) (hy : hexRadius y=(N+1:ℕ))
    (hX : hexRadius X=(n+1:ℕ)) (hY : hexRadius Y=(N+1:ℕ))
    (hpr : ∀ z ∈ p.support, hexRadius z=(n+1:ℕ) → z=x)
    (hpR : ∀ z ∈ p.support, hexRadius z=(N+1:ℕ) → z=y)
    (hqr : ∀ z ∈ q.support, hexRadius z=(n+1:ℕ) → z=X)
    (hqR : ∀ z ∈ q.support, hexRadius z=(N+1:ℕ) → z=Y) :
    ∃ (outer : triangularGraph.Walk y Y) (inner : triangularGraph.Walk X x),
      outer.IsPath ∧ inner.IsPath ∧
      (TriangularPlane.walkTrace outer ⊆ {z | hexGauge z=(N+1:ℕ)}) ∧
      (TriangularPlane.walkTrace inner ⊆ {z | hexGauge z=(n+1:ℕ)}) ∧
      (((p.append outer).append q.reverse).append inner).IsCycle := by
  obtain ⟨outer,ho,hout⟩ := hex_boundary_path N hy hY
  obtain ⟨inner,hi,hin⟩ := hex_boundary_path n hX hx
  refine ⟨outer,inner,ho,hi,level_path_trace_on_hex_cut N outer hout,
    level_path_trace_on_hex_cut n inner hin,?_⟩
  exact proper_paths_cut_boundary_cycle hexRadius (n+1:ℕ) (N+1:ℕ) (by omega)
    p q hp hq hdis hx hy hX hY hpr hpR hqr hqR outer inner ho hi hout hin

#print axioms proper_paths_cut_boundary_cycle
#print axioms hex_boundary_path
#print axioms hex_paths_have_cut_boundary_cycle

end ExceptionalTimes.PairSquareSewing
