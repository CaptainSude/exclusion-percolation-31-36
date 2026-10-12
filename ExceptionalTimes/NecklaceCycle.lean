import ExceptionalTimes.NecklaceExterior
import ExceptionalTimes.WiredBoundaryDictionary

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

/-- The four runs and their first three bridges form a simple open path. -/
def NecklaceShape.openPath (C : NecklaceShape) :
    triangularGraph.Walk (C.start 0) (C.finish 3) :=
  (C.run 0).append (.cons (C.bridge 0)
    ((C.run 1).append (.cons (C.bridge 1)
      ((C.run 2).append (.cons (C.bridge 2) (C.run 3))))))

theorem NecklaceShape.openPath_support (C : NecklaceShape) :
    C.openPath.support = (C.run 0).support ++ (C.run 1).support ++
      (C.run 2).support ++ (C.run 3).support := by
  unfold openPath
  rw [SimpleGraph.Walk.support_append]
  change (C.run 0).support ++
    ((C.run 1).append (.cons (C.bridge 1)
      ((C.run 2).append (.cons (C.bridge 2) (C.run 3))))).support = _
  rw [SimpleGraph.Walk.support_append]
  change (C.run 0).support ++ ((C.run 1).support ++
    ((C.run 2).append (.cons (C.bridge 2) (C.run 3))).support) = _
  rw [SimpleGraph.Walk.support_append]
  change (C.run 0).support ++ ((C.run 1).support ++
    ((C.run 2).support ++ (C.run 3).support)) = _
  simp only [List.append_assoc]

theorem NecklaceShape.openPath_isPath (C : NecklaceShape) : C.openPath.IsPath := by
  rw [SimpleGraph.Walk.isPath_def,C.openPath_support]
  have h0 := (C.simple 0).support_nodup
  have h1 := (C.simple 1).support_nodup
  have h2 := (C.simple 2).support_nodup
  have h3 := (C.simple 3).support_nodup
  have h01 := C.disjoint 0 1 (by decide)
  have h02 := C.disjoint 0 2 (by decide)
  have h03 := C.disjoint 0 3 (by decide)
  have h12 := C.disjoint 1 2 (by decide)
  have h13 := C.disjoint 1 3 (by decide)
  have h23 := C.disjoint 2 3 (by decide)
  simp only [List.nodup_append',List.disjoint_append_left]
  exact ⟨⟨⟨h0,h1,h01⟩,h2,⟨h02,h12⟩⟩,h3,⟨⟨h03,h13⟩,h23⟩⟩

/-- A literal graph cycle, assembled from the source's four runs. -/
def NecklaceShape.cycle (C : NecklaceShape) : triangularGraph.Walk (C.finish 3) (C.finish 3) :=
  .cons (C.bridge 3) C.openPath

theorem NecklaceShape.cycle_isCycle (C : NecklaceShape) : C.cycle.IsCycle := by
  change (SimpleGraph.Walk.cons (show triangularGraph.Adj (C.finish 3) (C.start 0) from C.bridge 3)
    C.openPath).IsCycle
  apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [SimpleGraph.Walk.tail_cons]
    exact (SimpleGraph.Walk.isPath_copy C.openPath _ _).mpr C.openPath_isPath
  · change 3 ≤ C.openPath.length + 1
    unfold openPath
    rw [SimpleGraph.Walk.length_append]
    change 3 ≤ (C.run 0).length +
      (((C.run 1).append (.cons (C.bridge 1)
        ((C.run 2).append (.cons (C.bridge 2) (C.run 3))))).length + 1) + 1
    rw [SimpleGraph.Walk.length_append]
    change 3 ≤ (C.run 0).length + ((C.run 1).length +
      (((C.run 2).append (.cons (C.bridge 2) (C.run 3))).length + 1) + 1) + 1
    omega

theorem NecklaceShape.cycle_support (C : NecklaceShape) : C.cycle.support.toFinset = C.vertices := by
  ext v
  change v ∈ (C.finish 3 :: C.openPath.support).toFinset ↔ v ∈ C.vertices
  simp only [List.mem_toFinset,List.mem_cons,
    C.openPath_support,List.mem_append,vertices,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ((h0 | h1) | h2) | h3)
    · exact ⟨3,(C.run 3).end_mem_support⟩
    · exact ⟨0,h0⟩
    · exact ⟨1,h1⟩
    · exact ⟨2,h2⟩
    · exact ⟨3,h3⟩
  · rintro ⟨i,hi⟩
    fin_cases i
    · exact Or.inr (Or.inl (Or.inl (Or.inl hi)))
    · exact Or.inr (Or.inl (Or.inl (Or.inr hi)))
    · exact Or.inr (Or.inl (Or.inr hi))
    · exact Or.inr (Or.inr hi)

/-- Intrinsic escape: the component avoiding the cycle reaches outside
every finite lattice box. This definition is independent of a chosen cut. -/
def NecklaceShape.EscapesToInfinity (C : NecklaceShape) (v : Site) : Prop :=
  ∀ R : ℕ, ∃ w ∉ latticeBox R, ∃ p : triangularGraph.Walk v w,
    ∀ z ∈ p.support, z ∉ C.vertices

theorem NecklaceShape.escape_from_outside_box (C : NecklaceShape) (n : ℕ)
    (hC : C.vertices ⊆ latticeBox n) {v : Site} (hv : v ∉ latticeBox n) :
    C.EscapesToInfinity v := by
  have hstep : ∀ k : ℕ, ∃ w ∉ latticeBox (n+k), ∃ p : triangularGraph.Walk v w,
      ∀ z ∈ p.support, z ∉ C.vertices := by
    intro k
    induction k with
    | zero =>
      refine ⟨v,?_,.nil,?_⟩
      · simpa only [Nat.add_zero] using hv
      · intro z hz
        have hzv : z = v := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
        exact fun hzC => hv (hzv ▸ hC hzC)
    | succ k ih =>
      obtain ⟨w,hw,p,hp⟩ := ih
      obtain ⟨u,hwu,hu⟩ := WiredBoundary.exists_adjacent_outside_larger_box hw
      have hwu' : triangularGraph.Adj w u := hwu
      have huC : u ∉ C.vertices := fun h => hu (latticeBox_mono (by omega) (hC h))
      refine ⟨u,?_,p.concat hwu',?_⟩
      · simpa only [Nat.add_succ] using hu
      · intro z hz
        rw [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hz
        exact hz.elim (hp z) (fun hzu => hzu ▸ huC)
  intro R
  obtain ⟨w,hw,p,hp⟩ := hstep R
  exact ⟨w,fun h => hw (latticeBox_mono (by omega) h),p,hp⟩

theorem NecklaceShape.exterior_box_iff_escapes (C : NecklaceShape) (n : ℕ)
    (hC : C.vertices ⊆ latticeBox n) (v : Site) :
    C.Exterior (latticeBox n) v ↔ C.EscapesToInfinity v := by
  constructor
  · rintro ⟨w,hw,p,hp⟩ R
    obtain ⟨u,hu,q,hq⟩ := C.escape_from_outside_box n hC hw R
    refine ⟨u,hu,p.append q,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    exact hz.elim (hp z) (hq z)
  · exact fun h => h n

/-- For a genuine enclosing square, the finite filled region is exactly
the nonescaping part of the graph complement, including the cycle. -/
theorem NecklaceShape.mem_filled_box_iff (C : NecklaceShape) (n : ℕ)
    (hC : C.vertices ⊆ latticeBox n) (v : Site) :
    v ∈ C.filled (latticeBox n) ↔ ¬ C.EscapesToInfinity v := by
  constructor
  · intro hv hesc
    exact (Finset.mem_filter.mp hv).2 ((C.exterior_box_iff_escapes n hC v).mpr hesc)
  · intro hesc
    have hv : v ∈ latticeBox n := by
      by_contra h
      exact hesc (C.escape_from_outside_box n hC h)
    exact Finset.mem_filter.mpr ⟨hv,fun h => hesc ((C.exterior_box_iff_escapes n hC v).mp h)⟩

theorem NecklaceShape.filled_box_independent (C : NecklaceShape) (m n : ℕ)
    (hm : C.vertices ⊆ latticeBox m) (hn : C.vertices ⊆ latticeBox n) :
    C.filled (latticeBox m) = C.filled (latticeBox n) := by
  ext v
  exact (C.mem_filled_box_iff m hm v).trans (C.mem_filled_box_iff n hn v).symm

/-- The opposite-color join, including every vertex of the white runs. -/
noncomputable def NecklaceShape.whiteJoinQuad (C : NecklaceShape) (Λ : Finset Site) : GraphQuad where
  domain := C.filled Λ
  firstSide := (C.run 1).support.toFinset
  secondSide := (C.run 3).support.toFinset

def complementConfiguration (ω : Configuration) : Configuration := fun v => !(ω v)

/-- The white join propagates by the actual two white connector paths,
just as the black join propagates by its two black connectors. -/
theorem necklace_white_join_propagates {C D : NecklaceShape} {Λ support : Finset Site}
    {ω : Configuration} (hCΛ : C.vertices ⊆ Λ) (hCD : C.filled Λ ⊆ D.filled Λ)
    (hCω : C.Colored ω) (hconn : NecklaceConnections C D Λ support ω)
    (hjoin : (C.whiteJoinQuad Λ).Crossing (complementConfiguration ω)) :
    (D.whiteJoinQuad Λ).Crossing (complementConfiguration ω) := by
  obtain ⟨s,t,p,he,_,hc,_⟩ := hconn
  obtain ⟨u,hu,v,hv,q,hq⟩ := hjoin
  have hrun (i : Fin 4) (hi : i.val % 2 ≠ 0) :
      ∀ z ∈ (C.run i).support, z ∈ D.filled Λ ∧ complementConfiguration ω z = true := by
    intro z hz
    refine ⟨hCD (C.vertices_subset_filled Λ hCΛ (C.run_mem_vertices i hz)),?_⟩
    have hzω := hCω i z hz
    simp only [hi,decide_false] at hzω
    simp only [complementConfiguration,hzω,Bool.not_false]
  have h1 : BlackJoined (D.filled Λ) (complementConfiguration ω) (s 1) u :=
    blackJoined_along_walk (C.run 1) (hrun 1 (by decide)) (he 1).1 (List.mem_toFinset.mp hu)
  have h3 : BlackJoined (D.filled Λ) (complementConfiguration ω) v (s 3) :=
    blackJoined_along_walk (C.run 3) (hrun 3 (by decide)) (List.mem_toFinset.mp hv) (he 3).1
  have hinner : BlackJoined (D.filled Λ) (complementConfiguration ω) u v :=
    BlackJoined.mono ⟨q,hq⟩ hCD
  have hp1 : BlackJoined (D.filled Λ) (complementConfiguration ω) (s 1) (t 1) := by
    refine ⟨p 1,?_⟩
    intro z hz
    refine ⟨(hc 1 z hz).2.1,?_⟩
    have hzω : ω z = false := (hc 1 z hz).2.2.2
    simp only [complementConfiguration,hzω,Bool.not_false]
  have hp3 : BlackJoined (D.filled Λ) (complementConfiguration ω) (s 3) (t 3) := by
    refine ⟨p 3,?_⟩
    intro z hz
    refine ⟨(hc 3 z hz).2.1,?_⟩
    have hzω : ω z = false := (hc 3 z hz).2.2.2
    simp only [complementConfiguration,hzω,Bool.not_false]
  obtain ⟨w,hw⟩ := (((hp1.symm.trans h1).trans hinner).trans h3).trans hp3
  exact ⟨t 1,List.mem_toFinset.mpr (he 1).2,t 3,List.mem_toFinset.mpr (he 3).2,w,hw⟩

#print axioms NecklaceShape.cycle_isCycle
#print axioms NecklaceShape.cycle_support
#print axioms NecklaceShape.mem_filled_box_iff
#print axioms NecklaceShape.filled_box_independent
#print axioms necklace_white_join_propagates

end ExceptionalTimes.PairSquareSewing

