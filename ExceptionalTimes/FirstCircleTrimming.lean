import ExceptionalTimes.CirclePathTrimming
import ExceptionalTimes.PathEndTrimming

/-! Circular trimming that retains the FIRST contact of the original
branch. This stronger certificate is needed when using a Jordan crossing
criterion; an arbitrary later annular excursion would not suffice. -/

namespace ExceptionalTimes.PairSquareSewing

open Annulus

theorem trim_first_circle (P : Probe) (hmesh : 2*P.mesh<P.innerRadius)
    {u v : Site} (p : triangularGraph.Walk u v) (hp : p.IsPath)
    (hu : P.radius u≤P.innerRadius) (hv : P.outerRadius≤P.radius v) :
    ∃ x,P.radius x≤P.innerRadius ∧ ∃ y,P.outerRadius≤P.radius y ∧
      ∃ before : triangularGraph.Walk u x,∃ q : triangularGraph.Walk x y,
        ∃ after : triangularGraph.Walk y v,
          (before.append q).append after=p ∧ q.IsPath ∧ q.IsSubwalk p ∧
          (∀ z∈q.support,z∈P.region) ∧
          (∀ z∈q.support,P.radius z≤P.innerRadius→z=x) ∧
          ∃ contact : ℂ,P.OuterContact q contact ∧ P.OuterContact (before.append q) contact := by
  obtain ⟨y,hy,full,after,hfull,hfullpath,hfullsub,hfirst⟩ :=
    first_arrival_prefix {z | P.outerRadius≤P.radius z} p hp hv
  obtain ⟨x,hx,q,before,hbefore,hq,hqsub,hlast⟩ :=
    last_departure_suffix {z | P.radius z≤P.innerRadius} full hfullpath hu
  have hio : P.innerRadius<P.outerRadius := by linarith [P.inner_pos,P.radii]
  have hxy : x≠y := by
    intro h
    subst y
    exact (not_le_of_gt hio) (hy.trans hx)
  have hnil : ¬q.Nil := fun h => hxy h.eq
  let last := q.adj_penultimate hnil
  have heq : q.dropLast.concat last=q := q.concat_dropLast last
  have heqfull : (before.append q.dropLast).concat last=full := by
    rw [←SimpleGraph.Walk.append_concat,heq,hbefore]
  have hpathfull : ((before.append q.dropLast).concat last).IsPath := by
    simpa only [heqfull] using hfullpath
  have hnoty : y∉(before.append q.dropLast).support :=
    ((SimpleGraph.Walk.isPath_concat last).mp hpathfull).2
  have hinsidefull : ∀ z∈(before.append q.dropLast).support,P.radius z<P.outerRadius := by
    intro z hz
    have hzs : z∈full.support := by
      rw [←heqfull]
      exact (before.append q.dropLast).support_subset_support_concat last hz
    by_contra h
    exact hnoty ((hfirst z hzs (by change P.outerRadius≤P.radius z; linarith)) ▸ hz)
  have hinside : ∀ z∈q.dropLast.support,P.radius z<P.outerRadius := by
    intro z hz
    apply hinsidefull z
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hz
  obtain ⟨contact,hedge,hcircle⟩ := edge_contact_exists P
    (hinside _ q.dropLast.end_mem_support) hy
  have hqcontact : P.OuterContact q contact :=
    ⟨q.penultimate,q.dropLast,last,heq.symm,hinside,hedge,hcircle⟩
  have hfullcontact : P.OuterContact (before.append q) contact := by
    rw [hbefore]
    exact ⟨q.penultimate,before.append q.dropLast,last,heqfull.symm,hinsidefull,hedge,hcircle⟩
  have hxlow : P.innerRadius-P.mesh<P.radius x :=
    walk_start_margin P.radius P.mesh P.radius_step q hnil P.innerRadius hlast
  have hyhigh : P.radius y<P.outerRadius+P.mesh := by
    have hs := P.radius_step last
    have hi := hinside _ q.dropLast.end_mem_support
    linarith
  have hregion : ∀ z∈q.support,z∈P.region := by
    intro z hz
    constructor
    · by_cases hi : P.radius z≤P.innerRadius
      · rw [hlast z hz hi]
        linarith
      · linarith [P.inner_pos]
    · by_cases ho : P.outerRadius≤P.radius z
      · rw [hfirst z (hqsub.support_subset hz) ho]
        linarith [P.inner_pos,P.radii]
      · linarith [P.inner_pos,P.radii]
  exact ⟨x,hx,y,hy,before,q,after,by rw [hbefore,hfull],hq,hqsub.trans hfullsub,
    hregion,hlast,contact,hqcontact,hfullcontact⟩

#print axioms trim_first_circle

end ExceptionalTimes.PairSquareSewing
