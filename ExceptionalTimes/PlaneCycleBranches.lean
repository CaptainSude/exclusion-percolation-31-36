import ExceptionalTimes.CycleBranches
import ExceptionalTimes.NecklacePlaneDisk

namespace ExceptionalTimes.TriangularPlane

open Set PairSquareSewing

theorem drawnEdge_reverse (u v : Site) : drawnEdge v u=drawnEdge u v := by
  ext z
  constructor
  all_goals
    rintro ⟨t,ht0,ht1,rfl⟩
    refine ⟨1-t,by linarith,by linarith,?_⟩
    exact (edgePoint_reverse _ _ t).symm

theorem walkTrace_single {u v : Site} (h : triangularGraph.Adj u v) :
    walkTrace (SimpleGraph.Walk.cons h .nil)=drawnEdge u v := by
  change drawnEdge u v∪{point v}=drawnEdge u v
  apply Set.union_eq_left.mpr
  rintro z rfl
  exact ⟨1,by norm_num,le_rfl,(edgePoint_one u v).symm⟩

theorem walkTrace_reverse {u v : Site} (p : triangularGraph.Walk u v) :
    walkTrace p.reverse=walkTrace p := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons,walkTrace_append,ih,walkTrace_single,drawnEdge_reverse]
    exact Set.union_comm _ _

theorem walkTrace_rotate {u v : Site} (p : triangularGraph.Walk u u)
    (hv : v∈p.support) : walkTrace (p.rotate v hv)=walkTrace p := by
  classical
  unfold SimpleGraph.Walk.rotate
  rw [walkTrace_append,Set.union_comm,←walkTrace_append,p.take_spec]

theorem plane_cycle_two_paths {u v w : Site} (c : triangularGraph.Walk u u)
    (hc : c.IsCycle) (hv : v∈c.support) (hw : w∈c.support) (hvw : v≠w) :
    ∃ p q : triangularGraph.Walk v w,p.IsPath ∧ q.IsPath ∧
      p.support⊆c.support ∧ q.support⊆c.support ∧
      (∀ z∈p.support,z∈q.support→z=v ∨ z=w) ∧
      (∀ z∈c.support,z∈p.support ∨ z∈q.support) ∧
      walkTrace c=walkTrace p∪walkTrace q ∧ (p.append q.reverse).IsCycle := by
  classical
  let C := c.rotate v hv
  have hC : C.IsCycle := hc.rotate hv
  have hwC : w∈C.support := (c.mem_support_rotate_iff v hv).mpr hw
  let p := C.takeUntil w hwC
  let d := C.dropUntil w hwC
  have happ : p.append d=C := C.take_spec hwC
  have hcycle : (p.append d).IsCycle := happ ▸ hC
  have hp : p.IsPath := hC.isPath_takeUntil hwC
  have hd : d.IsPath := hcycle.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne hvw)
  have hdis : List.Disjoint p.support.tail d.support.tail := by
    have hh := hcycle.support_nodup
    rw [SimpleGraph.Walk.tail_support_append,List.nodup_append'] at hh
    exact hh.2.2
  have hpC : p.support⊆C.support := C.support_takeUntil_subset_support hwC
  have hdC : d.support⊆C.support := C.support_dropUntil_subset_support hwC
  refine ⟨p,d.reverse,hp,hd.reverse,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact (c.mem_support_rotate_iff v hv).mp (hpC hz)
  · intro z hz
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
    exact (c.mem_support_rotate_iff v hv).mp (hdC hz)
  · intro z hzp hzd
    by_cases hzv : z=v
    · exact Or.inl hzv
    by_cases hzw : z=w
    · exact Or.inr hzw
    have hpz : z∈p.support.tail := by
      rw [←p.cons_tail_support,List.mem_cons] at hzp
      exact hzp.resolve_left hzv
    have hdz : z∈d.support.tail := by
      rw [SimpleGraph.Walk.support_reverse,List.mem_reverse,←d.cons_tail_support,List.mem_cons] at hzd
      exact hzd.resolve_left hzw
    exact False.elim (List.disjoint_left.mp hdis hpz hdz)
  · intro z hz
    have hzC := (c.mem_support_rotate_iff v hv).mpr hz
    change z∈C.support at hzC
    rw [←happ,SimpleGraph.Walk.mem_support_append_iff] at hzC
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hzC
  · rw [walkTrace_reverse,←walkTrace_append,happ]
    exact (walkTrace_rotate c hv).symm
  · simpa only [SimpleGraph.Walk.reverse_reverse] using hcycle

#print axioms plane_cycle_two_paths

end ExceptionalTimes.TriangularPlane
