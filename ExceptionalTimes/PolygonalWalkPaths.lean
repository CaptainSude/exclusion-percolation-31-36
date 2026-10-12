import ExceptionalTimes.TriangularPlane
import Mathlib.Analysis.Convex.PathConnected

open Set
open scoped Classical unitInterval

namespace ExceptionalTimes.TriangularPlane

theorem path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ z, z ∈ Set.range p → z ∈ Set.range q → z = b) :
    Function.Injective (p.trans q) := by
  intro s t h
  simp only [Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have he := congrArg Subtype.val (hp h)
    apply Subtype.ext
    dsimp at he
    linarith
  · have hsMem : p ⟨2*s,by constructor <;> linarith [s.2.1]⟩ ∈ Set.range q :=
      ⟨⟨2*t-1,by constructor <;> linarith [t.2.2]⟩,h.symm⟩
    have hm := hmeet _ ⟨_,rfl⟩ hsMem
    have hqe : q ⟨2*t-1,by constructor <;> linarith [t.2.2]⟩ = q 0 :=
      h.symm.trans (hm.trans q.source.symm)
    have he := congrArg Subtype.val (hq hqe)
    dsimp at he
    exfalso
    linarith
  · have htMem : p ⟨2*t,by constructor <;> linarith [t.2.1]⟩ ∈ Set.range q :=
      ⟨⟨2*s-1,by constructor <;> linarith [s.2.2]⟩,h⟩
    have hm := hmeet _ ⟨_,rfl⟩ htMem
    have hqe : q ⟨2*s-1,by constructor <;> linarith [s.2.2]⟩ = q 0 :=
      h.trans (hm.trans q.source.symm)
    have he := congrArg Subtype.val (hq hqe)
    dsimp at he
    exfalso
    linarith
  · have he := congrArg Subtype.val (hq h)
    apply Subtype.ext
    dsimp at he
    linarith

def edgePath (u v : Site) : Path (point u) (point v) where
  toFun t := edgePoint u v t
  continuous_toFun := (edgePoint_continuous u v).comp continuous_subtype_val
  source' := edgePoint_zero u v
  target' := edgePoint_one u v

theorem edgePath_injective {u v : Site} (h : TriangularAdj u v) :
    Function.Injective (edgePath u v) := by
  intro s t hst
  apply Subtype.ext
  exact edgePoint_injective h hst

theorem edgePath_range (u v : Site) :
    Set.range (edgePath u v) = {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = edgePoint u v t} := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,t.2.1,t.2.2,rfl⟩
  · rintro ⟨t,ht0,ht1,rfl⟩
    exact ⟨⟨t,ht0,ht1⟩,rfl⟩

/-- Traversal without a constant terminal interval: a one-edge walk is
represented by exactly one segment. This preserves injectivity. -/
noncomputable def walkPath : {u v : Site} → triangularGraph.Walk u v → Path (point u) (point v)
  | _,_,.nil => Path.refl _
  | a,_,@SimpleGraph.Walk.cons _ _ _ b _ _ .nil => edgePath a b
  | a,_,@SimpleGraph.Walk.cons _ _ _ b _ _ (.cons h p) =>
      (edgePath a b).trans (walkPath (.cons h p))

theorem walkPath_range {u v : Site} (p : triangularGraph.Walk u v) :
    Set.range (walkPath p) = walkTrace p := by
  induction p with
  | nil => simp [walkPath,walkTrace]
  | @cons a b c hab p ih =>
    cases p with
    | nil =>
      change Set.range (edgePath a b) = _
      rw [edgePath_range]
      change _ = _ ∪ {point b}
      symm
      apply Set.union_eq_left.mpr
      rintro z rfl
      exact ⟨1,by norm_num,le_rfl,(edgePoint_one a b).symm⟩
    | cons h p =>
      change Set.range ((edgePath a b).trans (walkPath (.cons h p))) = _
      rw [Path.trans_range,edgePath_range,ih]
      rfl

theorem walkPath_injective {u v : Site} (p : triangularGraph.Walk u v)
    (hp : p.IsPath) (hn : ¬p.Nil) : Function.Injective (walkPath p) := by
  induction p with
  | nil => exact False.elim (hn (by simp))
  | @cons a b c hab p ih =>
    have hpath : p.IsPath := hp.of_cons
    have ha : a ∉ p.support := (List.nodup_cons.mp hp.support_nodup).1
    cases p with
    | nil => exact edgePath_injective hab
    | @cons b d c hbd p =>
      apply path_trans_injective _ _ (edgePath_injective hab) (ih hpath (by simp))
      intro z hzedge hzpath
      have hsingle : z ∈ walkTrace (SimpleGraph.Walk.cons hab (.nil : triangularGraph.Walk b b)) := by
        exact Or.inl ((Set.ext_iff.mp (edgePath_range a b) z).mp hzedge)
      have htail : z ∈ walkTrace (SimpleGraph.Walk.cons hbd p) :=
        (Set.ext_iff.mp (walkPath_range _) z).mp hzpath
      apply walkTrace_intersection_only _ _ ?_ hsingle htail
      intro w hw hwp
      simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
        List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · exact False.elim (ha hwp)
      · rfl

#print axioms walkPath_range
#print axioms walkPath_injective

end ExceptionalTimes.TriangularPlane
