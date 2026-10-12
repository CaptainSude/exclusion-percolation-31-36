import ExceptionalTimes.HexCutTrimming
import Mathlib.Topology.Order.IntermediateValue

/-! Literal circular trimming of a simple lattice path. In particular,
the outer contact is on the first edge that reaches the common circle,
and all retained vertices lie in the actual probe region. -/

namespace ExceptionalTimes.PairSquareSewing

open Annulus

theorem position_distance_adj (e : ℝ) {u v : Site} (h : TriangularAdj u v) :
    dist (position e u) (position e v)=|e| := by
  rw [position,position,Complex.dist_eq,←mul_sub,norm_mul]
  rw [←Complex.dist_eq,(triangularAdj_iff_euclidean_distance u v).mp h]
  simp

theorem Probe.radius_step (P : Probe) {u v : Site} (h : TriangularAdj u v) :
    P.radius v ≤ P.radius u+P.mesh := by
  have ht := dist_triangle (position P.mesh v) (position P.mesh u) (position P.mesh P.center)
  rw [position_distance_adj P.mesh (triangularAdj_symm h),abs_of_pos P.mesh_pos] at ht
  change dist _ _≤dist _ _+_ 
  linarith

theorem walk_start_margin (f : Site→ℝ) (e : ℝ)
    (hstep : ∀ {u v},TriangularAdj u v→f v≤f u+e)
    {u v : Site} (p : triangularGraph.Walk u v) (hnil : ¬p.Nil) (r : ℝ)
    (hproper : ∀ z∈p.support,f z≤r→z=u) : r-e<f u := by
  cases p with
  | nil => exact False.elim (hnil (by simp))
  | @cons u w v huw p =>
    have hw : w∈(SimpleGraph.Walk.cons huw p).support :=
      List.mem_cons_of_mem _ p.start_mem_support
    have hnot : ¬f w≤r := by
      intro h
      exact triangularAdj_irrefl u ((hproper w hw h) ▸ huw)
    have hs := hstep huw
    linarith

theorem edge_contact_exists (P : Probe) {u v : Site}
    (hu : P.radius u<P.outerRadius) (hv : P.outerRadius≤P.radius v) :
    ∃ q∈edgeTrace P.mesh u v,dist q (position P.mesh P.center)=P.outerRadius := by
  let f : ℝ→ℂ := fun t => (1-(t:ℂ))*position P.mesh u+(t:ℂ)*position P.mesh v
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hc : Continuous (fun t => dist (f t) (position P.mesh P.center)) :=
    hf.dist continuous_const
  have hzero : dist (f 0) (position P.mesh P.center)=P.radius u := by simp [f,Probe.radius]
  have hone : dist (f 1) (position P.mesh P.center)=P.radius v := by simp [f,Probe.radius]
  have hbetween : P.outerRadius∈Set.Icc
      (dist (f 0) (position P.mesh P.center)) (dist (f 1) (position P.mesh P.center)) := by
    rw [hzero,hone]
    exact ⟨hu.le,hv⟩
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc.continuousOn hbetween
  exact ⟨f t,⟨t,ht.1,ht.2,rfl⟩,he⟩

theorem trim_path_circle (P : Probe) (hmesh : 2*P.mesh<P.innerRadius)
    {u v : Site} (p : triangularGraph.Walk u v) (hp : p.IsPath)
    (hu : P.radius u≤P.innerRadius) (hv : P.outerRadius≤P.radius v) :
    ∃ x, P.radius x≤P.innerRadius ∧ ∃ y,P.outerRadius≤P.radius y ∧
      ∃ q : triangularGraph.Walk x y,
        q.IsPath ∧ q.IsSubwalk p ∧
        (∀ z∈q.support,z∈P.region) ∧
        (∀ z∈q.support,P.radius z≤P.innerRadius→z=x) ∧
        ∃ contact : ℂ,P.OuterContact q contact := by
  obtain ⟨x,hx,y,hy,q,hq,hsub,hin,hout⟩ :=
    trim_path_between_sets {z | P.radius z≤P.innerRadius}
      {z | P.outerRadius≤P.radius z} p hp hu hv
  have hio : P.innerRadius<P.outerRadius := by linarith [P.inner_pos,P.radii]
  have hxy : x≠y := by
    intro he
    subst y
    exact (not_le_of_gt hio) (hy.trans hx)
  have hnil : ¬q.Nil := fun h => hxy h.eq
  have hxlow : P.innerRadius-P.mesh<P.radius x :=
    walk_start_margin P.radius P.mesh P.radius_step q hnil P.innerRadius hin
  have hnegrev : ∀ {a b},TriangularAdj a b→-P.radius b≤-P.radius a+P.mesh := by
    intro a b hab
    have h := P.radius_step (triangularAdj_symm hab)
    linarith
  have hyhigh : P.radius y<P.outerRadius+P.mesh := by
    have hrevnil : ¬q.reverse.Nil := fun h => hxy h.eq.symm
    have h := walk_start_margin (fun z => -P.radius z) P.mesh hnegrev q.reverse hrevnil
      (-P.outerRadius) (by
        intro z hz hzr
        rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
        exact hout z hz (by change P.outerRadius≤P.radius z; linarith))
    linarith
  have hbounds : ∀ z∈q.support,z∈P.region := by
    intro z hz
    constructor
    · by_cases hi : P.radius z≤P.innerRadius
      · rw [hin z hz hi]
        linarith
      · linarith [P.inner_pos]
    · by_cases ho : P.outerRadius≤P.radius z
      · rw [hout z hz ho]
        linarith [P.mesh_pos]
      · linarith [P.inner_pos]
  let last := q.adj_penultimate hnil
  have heq : q.dropLast.concat last=q := q.concat_dropLast last
  have hnoty : y∉q.dropLast.support :=
    ((SimpleGraph.Walk.isPath_concat last).mp (by simpa only [heq] using hq)).2
  have hpre : ∀ z∈q.dropLast.support,P.radius z<P.outerRadius := by
    intro z hz
    have hzs : z∈q.support := by
      rw [←heq]
      exact q.dropLast.support_subset_support_concat last hz
    by_contra h
    exact hnoty ((hout z hzs (by change P.outerRadius≤P.radius z; linarith)) ▸ hz)
  obtain ⟨contact,hcontact,hcircle⟩ :=
    edge_contact_exists P (hpre _ q.dropLast.end_mem_support) hy
  exact ⟨x,hx,y,hy,q,hq,hsub,hbounds,hin,contact,q.penultimate,q.dropLast,last,
    heq.symm,hpre,hcontact,hcircle⟩

#print axioms trim_path_circle

end ExceptionalTimes.PairSquareSewing
