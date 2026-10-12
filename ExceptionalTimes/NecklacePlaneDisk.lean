import ExceptionalTimes.NecklaceCycle
import ExceptionalTimes.TriangularPlane

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open TriangularPlane

def NecklaceShape.planeTrace (C : NecklaceShape) : Set (ℝ × ℝ) := walkTrace C.cycle

/-- The actual polygonal trace together with the bounded components of
its planar complement. Unlike the vertex-deletion graph hull, this
definition does not fill exterior pockets closed only by graph chords. -/
def NecklaceShape.planeDisk (C : NecklaceShape) : Set (ℝ × ℝ) :=
  {p | p ∈ C.planeTrace ∨ Bornology.IsBounded (connectedComponentIn C.planeTraceᶜ p)}

theorem vertex_mem_walkTrace {a b : Site} (p : triangularGraph.Walk a b)
    {u : Site} (hu : u ∈ p.support) : point u ∈ walkTrace p := by
  induction p with
  | @nil a =>
    have hua : u = a := List.mem_singleton.mp hu
    subst u
    exact rfl
  | @cons a b c hab p ih =>
    rcases List.mem_cons.mp hu with rfl | hu
    · exact Or.inl ⟨0,le_rfl,by norm_num,(edgePoint_zero u b).symm⟩
    · exact Or.inr (ih hu)

theorem point_mem_walkTrace_iff {a b : Site} (p : triangularGraph.Walk a b) (u : Site) :
    point u ∈ walkTrace p ↔ u ∈ p.support := by
  constructor
  · intro h
    rcases walkTrace_point_or_edge p h with ⟨v,hv,heq⟩ | ⟨v,hv,w,hw,hvw,t,ht0,ht1,heq⟩
    · exact point_injective heq ▸ hv
    · rcases vertex_on_edge_is_endpoint hvw ht0 ht1 heq.symm with h | h
      · exact h ▸ hv
      · exact h ▸ hw
  · exact vertex_mem_walkTrace p

theorem NecklaceShape.point_mem_planeTrace_iff (C : NecklaceShape) (u : Site) :
    point u ∈ C.planeTrace ↔ u ∈ C.vertices := by
  rw [planeTrace,point_mem_walkTrace_iff,← List.mem_toFinset,C.cycle_support]

theorem open_edge_trace_forces_endpoints {a b u v : Site} (p : triangularGraph.Walk a b)
    (huv : TriangularAdj u v) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ht : edgePoint u v t ∈ walkTrace p) : u ∈ p.support ∧ v ∈ p.support := by
  rcases walkTrace_point_or_edge p ht with ⟨w,hw,heq⟩ | ⟨w,hw,z,hz,hwz,s,hs0,hs1,heq⟩
  · exact False.elim (edge_interior_no_vertex huv w ht0 ht1 heq)
  · rcases closed_edge_intersection huv hwz ht0.le ht1.le hs0 hs1 heq with
      (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨x,_,_,hx⟩
    · exact ⟨hw,hz⟩
    · exact ⟨hz,hw⟩
    · exact False.elim (edge_interior_no_vertex huv x ht0 ht1 hx)

theorem NecklaceShape.half_edge_avoids_trace (C : NecklaceShape) {u v : Site}
    (huv : TriangularAdj u v) (hu : u ∉ C.vertices) :
    edgePoint u v '' Ico (0 : ℝ) 1 ⊆ C.planeTraceᶜ := by
  rintro _ ⟨t,⟨ht0,ht1⟩,rfl⟩ ht
  by_cases htzero : t = 0
  · subst t
    exact hu ((C.point_mem_planeTrace_iff u).mp (by simpa only [edgePoint_zero] using ht))
  · have hends := open_edge_trace_forces_endpoints C.cycle huv
      (lt_of_le_of_ne ht0 (Ne.symm htzero)) ht1 ht
    exact hu (by rw [← C.cycle_support]; exact List.mem_toFinset.mpr hends.1)

/-- A nonboundary endpoint and its edge midpoint are in the same actual
planar component, including when the other endpoint is on the cycle. -/
theorem NecklaceShape.component_endpoint_midpoint (C : NecklaceShape) {u v : Site}
    (huv : TriangularAdj u v) (hu : u ∉ C.vertices) :
    connectedComponentIn C.planeTraceᶜ (point u) =
      connectedComponentIn C.planeTraceᶜ (edgePoint u v (1/2)) := by
  have hc : IsPreconnected (edgePoint u v '' Ico (0 : ℝ) 1) :=
    isPreconnected_Ico.image _ (edgePoint_continuous u v).continuousOn
  have hstart : point u ∈ edgePoint u v '' Ico (0 : ℝ) 1 :=
    ⟨0,⟨le_rfl,by norm_num⟩,edgePoint_zero u v⟩
  have hmid : edgePoint u v (1/2) ∈ edgePoint u v '' Ico (0 : ℝ) 1 :=
    ⟨1/2,by norm_num,rfl⟩
  exact connectedComponentIn_eq (hc.subset_connectedComponentIn hstart
    (C.half_edge_avoids_trace huv hu) hmid)

def NecklaceShape.insideEdge (C : NecklaceShape) (u v : Site) : Prop :=
  edgePoint u v (1/2) ∈ C.planeDisk

theorem NecklaceShape.insideEdge_symm (C : NecklaceShape) (u v : Site) :
    C.insideEdge u v ↔ C.insideEdge v u := by
  have h : edgePoint v u (1/2) = edgePoint u v (1/2) := by
    convert edgePoint_reverse u v (1/2) using 1
    norm_num
  simp only [insideEdge,h]

/-- Boundary vertices belong to the disk, but a chord is classified by
its midpoint, so an exterior chord is retained as exterior. -/
theorem NecklaceShape.insideEdge_iff_endpoint (C : NecklaceShape) {u v : Site}
    (huv : TriangularAdj u v) (hu : u ∉ C.vertices) :
    C.insideEdge u v ↔ point u ∈ C.planeDisk := by
  have huT : point u ∉ C.planeTrace := fun h => hu ((C.point_mem_planeTrace_iff u).mp h)
  have hmT : edgePoint u v (1/2) ∉ C.planeTrace :=
    C.half_edge_avoids_trace huv hu ⟨1/2,by norm_num,rfl⟩
  change (_ ∨ _) ↔ (_ ∨ _)
  simp only [huT,hmT,false_or,C.component_endpoint_midpoint huv hu]

theorem NecklaceShape.insideEdge_endpoints (C : NecklaceShape) {u v : Site}
    (huv : TriangularAdj u v) (he : C.insideEdge u v) :
    point u ∈ C.planeDisk ∧ point v ∈ C.planeDisk := by
  have endpoint {a b : Site} (hab : TriangularAdj a b) (he : C.insideEdge a b) :
      point a ∈ C.planeDisk := by
    by_cases ha : a ∈ C.vertices
    · exact Or.inl ((C.point_mem_planeTrace_iff a).mpr ha)
    · exact (C.insideEdge_iff_endpoint hab ha).mp he
  exact ⟨endpoint huv he,endpoint (triangularAdj_symm huv) ((C.insideEdge_symm u v).mp he)⟩

theorem NecklaceShape.outsideEdge_endpoints (C : NecklaceShape) {u v : Site}
    (huv : TriangularAdj u v) (he : ¬ C.insideEdge u v) :
    (point u ∉ C.planeDisk ∨ u ∈ C.vertices) ∧
      (point v ∉ C.planeDisk ∨ v ∈ C.vertices) := by
  have endpoint {a b : Site} (hab : TriangularAdj a b) (he : ¬ C.insideEdge a b) :
      point a ∉ C.planeDisk ∨ a ∈ C.vertices := by
    by_cases ha : a ∈ C.vertices
    · exact Or.inr ha
    · exact Or.inl (fun h => he ((C.insideEdge_iff_endpoint hab ha).mpr h))
  exact ⟨endpoint huv he,endpoint (triangularAdj_symm huv)
    (fun h => he ((C.insideEdge_symm u v).mpr h))⟩

/-- If an open lattice edge meets a walk trace then this whole lattice
edge belongs to that trace. This excludes hidden partial intersections. -/
theorem open_edge_meets_trace_whole {a b u v : Site} (p : triangularGraph.Walk a b)
    (huv : TriangularAdj u v) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ht : edgePoint u v t ∈ walkTrace p) :
    ∀ s ∈ Icc (0 : ℝ) 1, edgePoint u v s ∈ walkTrace p := by
  induction p with
  | nil => exact False.elim (edge_interior_no_vertex huv _ ht0 ht1 ht)
  | @cons a b c hab p ih =>
    rcases ht with ⟨r,hr0,hr1,heq⟩ | ht
    · rcases closed_edge_intersection huv hab ht0.le ht1.le hr0 hr1 heq with
        (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | ⟨w,_,_,hw⟩
      · intro s hs
        exact Or.inl ⟨s,hs.1,hs.2,rfl⟩
      · intro s hs
        exact Or.inl ⟨1-s,by linarith [hs.2],by linarith [hs.1],(edgePoint_reverse u v s).symm⟩
      · exact False.elim (edge_interior_no_vertex huv w ht0 ht1 hw)
    · exact fun s hs => Or.inr (ih ht s hs)

theorem NecklaceShape.open_edge_component (C : NecklaceShape) {u v : Site}
    (huv : TriangularAdj u v) (hm : edgePoint u v (1/2) ∉ C.planeTrace)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    connectedComponentIn C.planeTraceᶜ (edgePoint u v (1/2)) =
      connectedComponentIn C.planeTraceᶜ (edgePoint u v t) := by
  have hc : IsPreconnected (edgePoint u v '' Ioo (0 : ℝ) 1) :=
    isPreconnected_Ioo.image _ (edgePoint_continuous u v).continuousOn
  have havoid : edgePoint u v '' Ioo (0 : ℝ) 1 ⊆ C.planeTraceᶜ := by
    rintro _ ⟨s,hs,rfl⟩ hsT
    exact hm (open_edge_meets_trace_whole C.cycle huv hs.1 hs.2 hsT (1/2) (by norm_num))
  have hmid : edgePoint u v (1/2) ∈ edgePoint u v '' Ioo (0 : ℝ) 1 :=
    ⟨1/2,by norm_num,rfl⟩
  exact connectedComponentIn_eq (hc.subset_connectedComponentIn hmid havoid ⟨t,⟨ht0,ht1⟩,rfl⟩)

/-- The midpoint classification equals literal containment of the whole
embedded edge in the planar disk, including both boundary endpoints. -/
theorem NecklaceShape.insideEdge_iff_whole_edge (C : NecklaceShape) {u v : Site}
    (huv : TriangularAdj u v) :
    C.insideEdge u v ↔ ∀ t ∈ Icc (0 : ℝ) 1, edgePoint u v t ∈ C.planeDisk := by
  constructor
  · intro he t ht
    by_cases ht0 : t = 0
    · subst t
      simpa only [edgePoint_zero] using (C.insideEdge_endpoints huv he).1
    by_cases ht1 : t = 1
    · subst t
      simpa only [edgePoint_one] using (C.insideEdge_endpoints huv he).2
    by_cases hm : edgePoint u v (1/2) ∈ C.planeTrace
    · exact Or.inl (open_edge_meets_trace_whole C.cycle huv (by norm_num) (by norm_num) hm t ht)
    · have hb : Bornology.IsBounded (connectedComponentIn C.planeTraceᶜ (edgePoint u v (1/2))) :=
        he.resolve_left hm
      apply Or.inr
      rw [← C.open_edge_component huv hm (lt_of_le_of_ne ht.1 (Ne.symm ht0))
        (lt_of_le_of_ne ht.2 ht1)]
      exact hb
  · exact fun h => h (1/2) (by norm_num)

def NecklaceShape.insideGraph (C : NecklaceShape) : SimpleGraph Site where
  Adj u v := TriangularAdj u v ∧ C.insideEdge u v
  symm := ⟨fun _ _ h => ⟨triangularAdj_symm h.1,(C.insideEdge_symm _ _).mp h.2⟩⟩
  loopless := ⟨fun u h => triangularAdj_irrefl u h.1⟩

def NecklaceShape.outsideGraph (C : NecklaceShape) : SimpleGraph Site where
  Adj u v := TriangularAdj u v ∧ ¬ C.insideEdge u v
  symm := ⟨fun _ _ h => ⟨triangularAdj_symm h.1,fun he => h.2 ((C.insideEdge_symm _ _).mpr he)⟩⟩
  loopless := ⟨fun u h => triangularAdj_irrefl u h.1⟩

theorem NecklaceShape.graph_partition (C : NecklaceShape) :
    C.insideGraph ⊔ C.outsideGraph = triangularGraph := by
  ext u v
  change (TriangularAdj u v ∧ C.insideEdge u v) ∨
    (TriangularAdj u v ∧ ¬ C.insideEdge u v) ↔ TriangularAdj u v
  constructor
  · exact fun h => h.elim And.left And.left
  · intro h
    by_cases he : C.insideEdge u v
    · exact Or.inl ⟨h,he⟩
    · exact Or.inr ⟨h,he⟩

theorem walkTrace_append {a b c : Site} (p : triangularGraph.Walk a b)
    (q : triangularGraph.Walk b c) : walkTrace (p.append q) = walkTrace p ∪ walkTrace q := by
  induction p with
  | nil =>
    change walkTrace q = {point _} ∪ walkTrace q
    symm
    apply union_eq_right.mpr
    intro z hz
    have hz' : z = point _ := hz
    rw [hz']
    exact vertex_mem_walkTrace q q.start_mem_support
  | cons h p ih =>
    rw [SimpleGraph.Walk.cons_append]
    change _ ∪ walkTrace (p.append q) = (_ ∪ walkTrace p) ∪ walkTrace q
    rw [ih,union_assoc]

def drawnEdge (u v : Site) : Set (ℝ × ℝ) :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = edgePoint u v t}

theorem NecklaceShape.openPath_trace (C : NecklaceShape) :
    walkTrace C.openPath = walkTrace (C.run 0) ∪ (drawnEdge (C.finish 0) (C.start 1) ∪
      (walkTrace (C.run 1) ∪ (drawnEdge (C.finish 1) (C.start 2) ∪
        (walkTrace (C.run 2) ∪ (drawnEdge (C.finish 2) (C.start 3) ∪ walkTrace (C.run 3)))))) := by
  unfold openPath
  rw [walkTrace_append]
  change walkTrace (C.run 0) ∪ (drawnEdge (C.finish 0) (C.start 1) ∪
    walkTrace ((C.run 1).append (.cons (C.bridge 1)
      ((C.run 2).append (.cons (C.bridge 2) (C.run 3)))))) = _
  rw [walkTrace_append]
  change walkTrace (C.run 0) ∪ (drawnEdge (C.finish 0) (C.start 1) ∪
    (walkTrace (C.run 1) ∪ (drawnEdge (C.finish 1) (C.start 2) ∪
      walkTrace ((C.run 2).append (.cons (C.bridge 2) (C.run 3)))))) = _
  rw [walkTrace_append]
  rfl

theorem NecklaceShape.run_trace_subset (C : NecklaceShape) (i : Fin 4) :
    walkTrace (C.run i) ⊆ C.planeTrace := by
  intro p hp
  change p ∈ drawnEdge (C.finish 3) (C.start 0) ∪ walkTrace C.openPath
  apply Or.inr
  rw [C.openPath_trace]
  fin_cases i
  · exact Or.inl hp
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))

/-- A literal walk lying on the cycle lifts to the edge-restricted
interior graph, with its actual colors. -/
theorem NecklaceShape.trace_monochrome_reachable (C : NecklaceShape) (ω : Configuration)
    (color : Bool) {a b : Site} (p : triangularGraph.Walk a b)
    (hp : walkTrace p ⊆ C.planeTrace) (hc : ∀ z ∈ p.support, ω z = color) :
    (Necklace.monochromeGraph C.insideGraph ω color).Reachable a b := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have hmid : edgePoint a b (1/2) ∈ C.planeTrace :=
      hp (Or.inl ⟨1/2,by norm_num,by norm_num,rfl⟩)
    have hab' : (Necklace.monochromeGraph C.insideGraph ω color).Adj a b :=
      ⟨⟨hab,Or.inl hmid⟩,hc a (List.mem_cons_self ..),
        hc b (List.mem_cons_of_mem _ p.start_mem_support)⟩
    exact hab'.reachable.trans (ih (fun _ h => hp (Or.inr h))
      (fun z hz => hc z (List.mem_cons_of_mem _ hz)))

theorem NecklaceShape.run_reachable_inside (C : NecklaceShape) {ω : Configuration}
    (hω : C.Colored ω) (i : Fin 4) :
    (Necklace.monochromeGraph C.insideGraph ω (decide (i.val % 2 = 0))).Reachable
      (C.start i) (C.finish i) :=
  C.trace_monochrome_reachable ω _ (C.run i) (C.run_trace_subset i) (hω i)

#print axioms NecklaceShape.component_endpoint_midpoint
#print axioms NecklaceShape.insideEdge_endpoints
#print axioms NecklaceShape.outsideEdge_endpoints
#print axioms NecklaceShape.insideEdge_iff_whole_edge
#print axioms NecklaceShape.graph_partition
#print axioms NecklaceShape.run_reachable_inside

end ExceptionalTimes.PairSquareSewing
