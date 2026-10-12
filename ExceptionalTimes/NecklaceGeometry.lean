import ExceptionalTimes.PolygonLocalChange
import ExceptionalTimes.SourceTrialSymmetry

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

/-- Four nonempty simple runs, joined cyclically by one edge apiece.
The run supports are pairwise disjoint; no selected-path randomness
is introduced by this witness type. Colors are a separate property. -/
structure NecklaceShape where
  start : Fin 4 → Site
  finish : Fin 4 → Site
  run : ∀ i, triangularGraph.Walk (start i) (finish i)
  simple : ∀ i, (run i).IsPath
  disjoint : ∀ i j, i ≠ j → List.Disjoint (run i).support (run j).support
  bridge : ∀ i, TriangularAdj (finish i) (start (i+1))

def NecklaceShape.vertices (C : NecklaceShape) : Finset Site :=
  Finset.univ.biUnion (fun i => (C.run i).support.toFinset)

def NecklaceShape.Colored (C : NecklaceShape) (ω : Configuration) : Prop :=
  ∀ i v, v ∈ (C.run i).support → ω v = decide (i.val % 2 = 0)

theorem NecklaceShape.run_mem_vertices (C : NecklaceShape) (i : Fin 4)
    {v : Site} (hv : v ∈ (C.run i).support) : v ∈ C.vertices := by
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr hv⟩

theorem NecklaceShape.start_mem_vertices (C : NecklaceShape) (i : Fin 4) :
    C.start i ∈ C.vertices := C.run_mem_vertices i (C.run i).start_mem_support

theorem NecklaceShape.finish_mem_vertices (C : NecklaceShape) (i : Fin 4) :
    C.finish i ∈ C.vertices := C.run_mem_vertices i (C.run i).end_mem_support

/-- A site is outside a cycle if a finite graph path avoiding all its
vertices reaches outside the chosen finite enclosing box. -/
def NecklaceShape.Exterior (C : NecklaceShape) (Λ : Finset Site) (v : Site) : Prop :=
  ∃ w ∉ Λ, ∃ p : triangularGraph.Walk v w, ∀ z ∈ p.support, z ∉ C.vertices

noncomputable def NecklaceShape.filled (C : NecklaceShape) (Λ : Finset Site) : Finset Site :=
  Λ.filter (fun v => ¬ C.Exterior Λ v)

theorem NecklaceShape.not_exterior_of_mem (C : NecklaceShape) (Λ : Finset Site)
    {v : Site} (hv : v ∈ C.vertices) : ¬ C.Exterior Λ v := by
  rintro ⟨w,_,p,hp⟩
  exact hp v p.start_mem_support hv

theorem NecklaceShape.vertices_subset_filled (C : NecklaceShape) (Λ : Finset Site)
    (hC : C.vertices ⊆ Λ) : C.vertices ⊆ C.filled Λ := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨hC hv,C.not_exterior_of_mem Λ hv⟩

theorem NecklaceShape.exterior_of_outside (C : NecklaceShape) (Λ : Finset Site)
    {v : Site} (hv : v ∉ Λ) (hvC : v ∉ C.vertices) : C.Exterior Λ v := by
  refine ⟨v,hv,SimpleGraph.Walk.nil,?_⟩
  intro z hz
  have hzv : z = v := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
  simpa only [hzv] using hvC

theorem NecklaceShape.exterior_step (C : NecklaceShape) (Λ : Finset Site)
    {u v : Site} (h : TriangularAdj u v) (hu : u ∉ C.vertices)
    (hv : C.Exterior Λ v) : C.Exterior Λ u := by
  obtain ⟨w,hw,p,hp⟩ := hv
  refine ⟨w,hw,SimpleGraph.Walk.cons h p,?_⟩
  intro z hz
  change z ∈ u :: p.support at hz
  have hz' := List.mem_cons.mp hz
  rcases hz' with rfl | hz
  · exact hu
  · exact hp z hz

theorem NecklaceShape.exterior_of_not_filled (C : NecklaceShape) (Λ : Finset Site)
    (hC : C.vertices ⊆ Λ) {v : Site} (hv : v ∉ C.filled Λ) : C.Exterior Λ v := by
  by_cases hvΛ : v ∈ Λ
  · by_contra h
    exact hv (Finset.mem_filter.mpr ⟨hvΛ,h⟩)
  · exact C.exterior_of_outside Λ hvΛ (fun h => hvΛ (hC h))

/-- Literal cut property of the filled disk, proved from graph paths:
an edge cannot leave it without starting on the cycle. -/
theorem NecklaceShape.edge_exits_on_cycle (C : NecklaceShape) (Λ : Finset Site)
    (hC : C.vertices ⊆ Λ) {u v : Site} (hu : u ∈ C.filled Λ)
    (hv : v ∉ C.filled Λ) (huv : TriangularAdj u v) : u ∈ C.vertices := by
  by_contra huC
  exact (Finset.mem_filter.mp hu).2
    (C.exterior_step Λ huv huC (C.exterior_of_not_filled Λ hC hv))

/-- The actual inner-join test includes every run vertex, matching
the source's explicit convention. -/
noncomputable def NecklaceShape.joinQuad (C : NecklaceShape) (Λ : Finset Site) : GraphQuad where
  domain := C.filled Λ
  firstSide := (C.run 0).support.toFinset
  secondSide := (C.run 2).support.toFinset

theorem NecklaceShape.join_sides_in_domain (C : NecklaceShape) (Λ : Finset Site)
    (hC : C.vertices ⊆ Λ) :
    (C.joinQuad Λ).firstSide ⊆ (C.joinQuad Λ).domain ∧
    (C.joinQuad Λ).secondSide ⊆ (C.joinQuad Λ).domain := by
  constructor <;> intro v hv
  · exact C.vertices_subset_filled Λ hC (C.run_mem_vertices 0 (List.mem_toFinset.mp hv))
  · exact C.vertices_subset_filled Λ hC (C.run_mem_vertices 2 (List.mem_toFinset.mp hv))

theorem NecklaceShape.colored_join_terminals (C : NecklaceShape) (Λ : Finset Site)
    {ω : Configuration} (hω : C.Colored ω) :
    (∀ v ∈ (C.joinQuad Λ).firstSide, ω v = true) ∧
    (∀ v ∈ (C.joinQuad Λ).secondSide, ω v = true) := by
  constructor <;> intro v hv
  · exact hω 0 v (List.mem_toFinset.mp hv)
  · exact hω 2 v (List.mem_toFinset.mp hv)

/-- Actual four simple, mutually disjoint alternating paths connecting
corresponding runs. All color coordinates lie in the prescribed support. -/
def NecklaceConnections (C D : NecklaceShape) (Λ support : Finset Site) (ω : Configuration) : Prop :=
  ∃ start finish : Fin 4 → Site,
    ∃ path : ∀ i, triangularGraph.Walk (start i) (finish i),
      (∀ i, start i ∈ (C.run i).support ∧ finish i ∈ (D.run i).support) ∧
      (∀ i, (path i).IsPath) ∧
      (∀ i v, v ∈ (path i).support → v ∈ support ∧ v ∈ D.filled Λ ∧
        (v ∈ C.filled Λ → v ∈ C.vertices) ∧ ω v = decide (i.val % 2 = 0)) ∧
      (∀ i j, i ≠ j → List.Disjoint (path i).support (path j).support)

theorem NecklaceShape.colored_congr (C : NecklaceShape) (support : Finset Site)
    (hC : C.vertices ⊆ support) {ω η : Configuration} (h : Set.EqOn ω η (support : Set Site)) :
    C.Colored ω ↔ C.Colored η := by
  have hh : ∀ i v, v ∈ (C.run i).support → ω v = η v := fun i v hv => h (hC (C.run_mem_vertices i hv))
  constructor <;> intro hc i v hv
  · rw [← hh i v hv]
    exact hc i v hv
  · rw [hh i v hv]
    exact hc i v hv

theorem necklaceConnections_congr (C D : NecklaceShape) (Λ support : Finset Site)
    {ω η : Configuration} (h : Set.EqOn ω η (support : Set Site)) :
    NecklaceConnections C D Λ support ω ↔ NecklaceConnections C D Λ support η := by
  have forward {a b : Configuration} (hab : Set.EqOn a b (support : Set Site)) :
      NecklaceConnections C D Λ support a → NecklaceConnections C D Λ support b := by
    rintro ⟨s,t,p,he,hp,hc,hd⟩
    refine ⟨s,t,p,he,hp,?_,hd⟩
    intro i v hv
    exact ⟨(hc i v hv).1,(hc i v hv).2.1,(hc i v hv).2.2.1,
      (hab (hc i v hv).1).symm.trans (hc i v hv).2.2.2⟩
  exact ⟨forward h,forward h.symm⟩

/-- The literal triangular-model necklace relation inside one trial.
The finite enclosing box and sleeve sets are deterministic. Geometry,
enclosure and nesting do not depend on the sampled colors. -/
def NecklaceSeamRelation {Λ : Finset Site}
    (support innerSleeve outerSleeve pocket : Finset Site)
    (C D : NecklaceShape) (bits : ↥Λ → Bool) : Prop :=
  C.vertices ⊆ innerSleeve ∧ D.vertices ⊆ outerSleeve ∧
  C.vertices ⊆ Λ ∧ D.vertices ⊆ Λ ∧
  pocket ⊆ C.filled Λ ∧ C.filled Λ ⊆ D.filled Λ ∧
  C.Colored (complete bits) ∧ D.Colored (complete bits) ∧
  NecklaceConnections C D Λ support (complete bits)

theorem necklaceSeamRelation_supported {Λ : Finset Site}
    (support innerSleeve outerSleeve pocket : Finset Site)
    (hin : innerSleeve ⊆ support) (hout : outerSleeve ⊆ support) :
    SupportedSeamRelation support (NecklaceSeamRelation (Λ := Λ) support innerSleeve outerSleeve pocket) := by
  intro C D ω η h
  have heq : Set.EqOn (complete ω) (complete η) (support : Set Site) := by
    intro v hv
    by_cases hΛ : v ∈ Λ
    · simpa [complete,hΛ] using h ⟨v,hΛ⟩ hv
    · simp [complete,hΛ]
  have forward {a b : ↥Λ → Bool} (hab : Set.EqOn (complete a) (complete b) (support : Set Site)) :
      NecklaceSeamRelation support innerSleeve outerSleeve pocket C D a →
      NecklaceSeamRelation support innerSleeve outerSleeve pocket C D b := by
    rintro ⟨hCi,hDo,hCΛ,hDΛ,hp,hCD,hCa,hDa,hconn⟩
    exact ⟨hCi,hDo,hCΛ,hDΛ,hp,hCD,
      (C.colored_congr support (hCi.trans hin) hab).mp hCa,
      (D.colored_congr support (hDo.trans hout) hab).mp hDa,
      (necklaceConnections_congr C D Λ support hab).mp hconn⟩
  exact ⟨forward heq,forward heq.symm⟩

/-- With this actual geometric witness relation, the source's all-four
success event has the required exact support and exchange invariance. -/
noncomputable def necklaceSuccess {Λ : Finset Site}
    (inside support innerSleeve outerSleeve pocket : Finset Site) : Sources Λ → Bool :=
  fourWayTest inside (NecklaceSeamRelation support innerSleeve outerSleeve pocket)

theorem necklaceSuccess_supported {Λ : Finset Site}
    (inside support innerSleeve outerSleeve pocket : Finset Site)
    (hin : innerSleeve ⊆ support) (hout : outerSleeve ⊆ support) :
    SupportedSourceTest support (necklaceSuccess (Λ := Λ) inside support innerSleeve outerSleeve pocket) :=
  fourWayTest_supported support inside _ (necklaceSeamRelation_supported support innerSleeve outerSleeve pocket hin hout)

theorem necklaceSuccess_seamSwap {Λ : Finset Site}
    (inside support innerSleeve outerSleeve pocket : Finset Site) (ω : Sources Λ) :
    necklaceSuccess inside support innerSleeve outerSleeve pocket (seamSwap inside ω) =
      necklaceSuccess inside support innerSleeve outerSleeve pocket ω :=
  fourWayTest_seamSwap inside _ ω

def BlackJoined (D : Finset Site) (ω : Configuration) (u v : Site) : Prop :=
  ∃ p : triangularGraph.Walk u v, ∀ z ∈ p.support, z ∈ D ∧ ω z = true

theorem BlackJoined.symm {D : Finset Site} {ω : Configuration} {u v : Site}
    (h : BlackJoined D ω u v) : BlackJoined D ω v u := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p.reverse,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
  exact hp z hz

theorem BlackJoined.trans {D : Finset Site} {ω : Configuration} {u v w : Site}
    (huv : BlackJoined D ω u v) (hvw : BlackJoined D ω v w) : BlackJoined D ω u w := by
  obtain ⟨p,hp⟩ := huv
  obtain ⟨q,hq⟩ := hvw
  refine ⟨p.append q,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  exact hz.elim (hp z) (hq z)

theorem BlackJoined.mono {D E : Finset Site} {ω : Configuration} {u v : Site}
    (h : BlackJoined D ω u v) (hDE : D ⊆ E) : BlackJoined E ω u v := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun z hz => ⟨hDE (hp z hz).1,(hp z hz).2⟩⟩

theorem blackJoined_along_walk {D : Finset Site} {ω : Configuration} {a b u v : Site}
    (p : triangularGraph.Walk a b) (hp : ∀ z ∈ p.support, z ∈ D ∧ ω z = true)
    (hu : u ∈ p.support) (hv : v ∈ p.support) : BlackJoined D ω u v := by
  have hu' : BlackJoined D ω a u :=
    ⟨p.takeUntil u hu,fun z hz => hp z (p.support_takeUntil_subset_support hu hz)⟩
  have hv' : BlackJoined D ω a v :=
    ⟨p.takeUntil v hv,fun z hz => hp z (p.support_takeUntil_subset_support hv hz)⟩
  exact hu'.symm.trans hv'

/-- The black join always propagates outward along the actual black
connector paths. This half of bit transmission is proved by explicit
walk concatenation; the reverse implication uses planar duality. -/
theorem necklace_join_propagates {C D : NecklaceShape} {Λ support : Finset Site}
    {ω : Configuration} (hCΛ : C.vertices ⊆ Λ) (hCD : C.filled Λ ⊆ D.filled Λ)
    (hCω : C.Colored ω) (hconn : NecklaceConnections C D Λ support ω)
    (hjoin : (C.joinQuad Λ).Crossing ω) : (D.joinQuad Λ).Crossing ω := by
  obtain ⟨s,t,p,he,_,hc,_⟩ := hconn
  obtain ⟨u,hu,v,hv,q,hq⟩ := hjoin
  have hrun (i : Fin 4) (hi : i.val % 2 = 0) :
      ∀ z ∈ (C.run i).support, z ∈ D.filled Λ ∧ ω z = true := by
    intro z hz
    refine ⟨hCD (C.vertices_subset_filled Λ hCΛ (C.run_mem_vertices i hz)),?_⟩
    simpa only [hi,decide_true] using hCω i z hz
  have h0 : BlackJoined (D.filled Λ) ω (s 0) u :=
    blackJoined_along_walk (C.run 0) (hrun 0 rfl) (he 0).1 (List.mem_toFinset.mp hu)
  have h2 : BlackJoined (D.filled Λ) ω v (s 2) :=
    blackJoined_along_walk (C.run 2) (hrun 2 rfl) (List.mem_toFinset.mp hv) (he 2).1
  have hinner : BlackJoined (D.filled Λ) ω u v :=
    BlackJoined.mono ⟨q,hq⟩ hCD
  have hp0 : BlackJoined (D.filled Λ) ω (s 0) (t 0) :=
    ⟨p 0,fun z hz => ⟨(hc 0 z hz).2.1,(hc 0 z hz).2.2.2⟩⟩
  have hp2 : BlackJoined (D.filled Λ) ω (s 2) (t 2) :=
    ⟨p 2,fun z hz => ⟨(hc 2 z hz).2.1,(hc 2 z hz).2.2.2⟩⟩
  obtain ⟨w,hw⟩ := (((hp0.symm.trans h0).trans hinner).trans h2).trans hp2
  exact ⟨t 0,List.mem_toFinset.mpr (he 0).2,t 2,List.mem_toFinset.mpr (he 2).2,w,hw⟩

#print axioms NecklaceShape.edge_exits_on_cycle
#print axioms NecklaceShape.join_sides_in_domain
#print axioms necklaceSeamRelation_supported
#print axioms necklaceSuccess_seamSwap
#print axioms necklace_join_propagates

end ExceptionalTimes.PairSquareSewing
