import Mathlib.Combinatorics.SimpleGraph.Paths

/-! The two literal simple branches of a cycle between distinct marked
vertices. This is purely graph theoretic and asserts no planar order. -/

namespace ExceptionalTimes.CycleBranches

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

theorem path_two_branches (p : G.Walk u w) (hp : p.IsPath) (hv : v∈p.support) :
    ∃ q : G.Walk v u, ∃ r : G.Walk v w,
      q.IsPath ∧ r.IsPath ∧ q.support⊆p.support ∧ r.support⊆p.support ∧
      ∀ z∈q.support,z∈r.support → z=v := by
  classical
  let q := p.takeUntil v hv
  let r := p.dropUntil v hv
  have happ : q.append r=p := p.take_spec hv
  have hh : (q.append r).IsPath := happ ▸ hp
  refine ⟨q.reverse,r,(hp.takeUntil hv).reverse,hp.dropUntil hv,?_,
    p.support_dropUntil_subset_support hv,?_⟩
  · intro z hz
    rw [Walk.support_reverse,List.mem_reverse] at hz
    exact p.support_takeUntil_subset_support hv hz
  · intro z hzq hzr
    by_contra hzv
    rw [Walk.support_reverse,List.mem_reverse] at hzq
    exact (hh.ne_of_mem_support_of_append hzv hzq hzr) rfl

theorem cycle_two_paths (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v∈c.support) (huv : u≠v) :
    ∃ p q : G.Walk u v, p.IsPath ∧ q.IsPath ∧
      p.support⊆c.support ∧ q.support⊆c.support ∧
      (∀ z∈p.support,z∈q.support → z=u ∨ z=v) ∧
      (∀ z∈c.support,z∈p.support ∨ z∈q.support) := by
  classical
  let p := c.takeUntil v hv
  let d := c.dropUntil v hv
  have happ : p.append d=c := c.take_spec hv
  have hcycle : (p.append d).IsCycle := happ ▸ hc
  have hp : p.IsPath := hc.isPath_takeUntil hv
  have hd : d.IsPath := hcycle.isPath_of_append_right (Walk.not_nil_of_ne huv)
  have hdis : List.Disjoint p.support.tail d.support.tail := by
    have hh := hcycle.support_nodup
    rw [Walk.tail_support_append,List.nodup_append'] at hh
    exact hh.2.2
  refine ⟨p,d.reverse,hp,hd.reverse,c.support_takeUntil_subset_support hv,?_,?_,?_⟩
  · intro z hz
    rw [Walk.support_reverse,List.mem_reverse] at hz
    exact c.support_dropUntil_subset_support hv hz
  · intro z hzp hzd
    by_cases hzu : z=u
    · exact Or.inl hzu
    by_cases hzv : z=v
    · exact Or.inr hzv
    have hpz : z∈p.support.tail := by
      rw [← p.cons_tail_support,List.mem_cons] at hzp
      exact hzp.resolve_left hzu
    have hdz : z∈d.support.tail := by
      rw [Walk.support_reverse,List.mem_reverse,← d.cons_tail_support,List.mem_cons] at hzd
      exact hzd.resolve_left hzv
    exact False.elim (List.disjoint_left.mp hdis hpz hdz)
  · intro z hz
    rw [←happ,Walk.mem_support_append_iff] at hz
    simpa only [Walk.support_reverse,List.mem_reverse] using hz

theorem cycle_two_paths_from_member (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v∈c.support) (hw : w∈c.support) (hvw : v≠w) :
    ∃ p q : G.Walk v w, p.IsPath ∧ q.IsPath ∧
      p.support⊆c.support ∧ q.support⊆c.support ∧
      (∀ z∈p.support,z∈q.support → z=v ∨ z=w) ∧
      (∀ z∈c.support,z∈p.support ∨ z∈q.support) := by
  classical
  have hw' : w∈(c.rotate v hv).support := (c.mem_support_rotate_iff v hv).mpr hw
  obtain ⟨p,q,hp,hq,hpc,hqc,hdis,hcover⟩ := cycle_two_paths (c.rotate v hv) (hc.rotate hv) hw' hvw
  refine ⟨p,q,hp,hq,?_,?_,hdis,?_⟩
  · intro z hz
    exact (c.mem_support_rotate_iff v hv).mp (hpc hz)
  · intro z hz
    exact (c.mem_support_rotate_iff v hv).mp (hqc hz)
  · intro z hz
    exact hcover z ((c.mem_support_rotate_iff v hv).mpr hz)

#print axioms cycle_two_paths
#print axioms cycle_two_paths_from_member
#print axioms path_two_branches

end ExceptionalTimes.CycleBranches
