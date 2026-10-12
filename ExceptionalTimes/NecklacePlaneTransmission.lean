import ExceptionalTimes.NecklacePlaneDisk

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open TriangularPlane

theorem walkTrace_takeUntil_subset {a b u : Site} (p : triangularGraph.Walk a b)
    (hu : u ∈ p.support) : walkTrace (p.takeUntil u hu) ⊆ walkTrace p := by
  conv_rhs => rw [← p.take_spec hu,walkTrace_append]
  exact subset_union_left

theorem NecklaceShape.run_vertices_reachable_inside (C : NecklaceShape) {ω : Configuration}
    (hω : C.Colored ω) (i : Fin 4) {u v : Site}
    (hu : u ∈ (C.run i).support) (hv : v ∈ (C.run i).support) :
    (Necklace.monochromeGraph C.insideGraph ω (decide (i.val % 2 = 0))).Reachable u v := by
  have fromStart (w : Site) (hw : w ∈ (C.run i).support) :
      (Necklace.monochromeGraph C.insideGraph ω (decide (i.val % 2 = 0))).Reachable (C.start i) w :=
    C.trace_monochrome_reachable ω _ ((C.run i).takeUntil w hw)
      ((walkTrace_takeUntil_subset _ hw).trans (C.run_trace_subset i))
      (fun z hz => hω i z ((C.run i).support_takeUntil_subset_support hw hz))
  exact (fromStart u hu).symm.trans (fromStart v hv)

/-- The genuine disk join uses only edges whose whole geometric trace
lies in the planar disk. Exterior chords are not part of this bit. -/
def NecklaceShape.PlaneJoined (C : NecklaceShape) (ω : Configuration) : Prop :=
  (Necklace.monochromeGraph C.insideGraph ω true).Reachable (C.start 0) (C.start 2)

noncomputable def NecklaceShape.planeJoinBit (C : NecklaceShape) (ω : Configuration) : Bool :=
  decide (C.PlaneJoined ω)

theorem NecklaceShape.plane_boundary_transport (C : NecklaceShape) {ω η : Configuration}
    (hω : C.Colored ω) (hη : C.Colored η) (hbit : C.PlaneJoined ω → C.PlaneJoined η)
    {u v : Site} (hu : u ∈ C.vertices) (hv : v ∈ C.vertices)
    (huω : ω u = true) (hvω : ω v = true)
    (h : (Necklace.monochromeGraph C.insideGraph ω true).Reachable u v) :
    (Necklace.monochromeGraph C.insideGraph η true).Reachable u v := by
  have run0 (a : Configuration) (ha : C.Colored a) {x y : Site}
      (hx : x ∈ (C.run 0).support) (hy : y ∈ (C.run 0).support) :
      (Necklace.monochromeGraph C.insideGraph a true).Reachable x y :=
    C.run_vertices_reachable_inside ha 0 hx hy
  have run2 (a : Configuration) (ha : C.Colored a) {x y : Site}
      (hx : x ∈ (C.run 2).support) (hy : y ∈ (C.run 2).support) :
      (Necklace.monochromeGraph C.insideGraph a true).Reachable x y :=
    C.run_vertices_reachable_inside ha 2 hx hy
  rcases C.black_mem_runs hω hu huω with hu0 | hu2 <;>
    rcases C.black_mem_runs hω hv hvω with hv0 | hv2
  · exact run0 η hη hu0 hv0
  · have hj : C.PlaneJoined ω :=
      ((run0 ω hω (C.run 0).start_mem_support hu0).trans h).trans
        (run2 ω hω hv2 (C.run 2).start_mem_support)
    exact ((run0 η hη hu0 (C.run 0).start_mem_support).trans (hbit hj)).trans
      (run2 η hη (C.run 2).start_mem_support hv2)
  · have hj : C.PlaneJoined ω :=
      ((run0 ω hω (C.run 0).start_mem_support hv0).trans h.symm).trans
        (run2 ω hω hu2 (C.run 2).start_mem_support)
    exact (((run0 η hη hv0 (C.run 0).start_mem_support).trans (hbit hj)).trans
      (run2 η hη (C.run 2).start_mem_support hu2)).symm
  · exact run2 η hη hu2 hv2

def GraphQuad.domainGraph (Q : GraphQuad) : SimpleGraph Site where
  Adj u v := TriangularAdj u v ∧ u ∈ Q.domain ∧ v ∈ Q.domain
  symm := ⟨fun _ _ h => ⟨triangularAdj_symm h.1,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun u h => triangularAdj_irrefl u h.1⟩

def GraphQuad.blackGraph (Q : GraphQuad) (ω : Configuration) : SimpleGraph Site :=
  Necklace.monochromeGraph Q.domainGraph ω true

theorem GraphQuad.blackJoined_iff (Q : GraphQuad) (ω : Configuration) (u v : Site) :
    BlackJoined Q.domain ω u v ↔ u ∈ Q.domain ∧ ω u = true ∧ (Q.blackGraph ω).Reachable u v := by
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨(hp u p.start_mem_support).1,(hp u p.start_mem_support).2,?_⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih =>
      have ha := hp a (List.mem_cons_self ..)
      have hb := hp b (List.mem_cons_of_mem _ p.start_mem_support)
      have hadj : (Q.blackGraph ω).Adj a b := ⟨⟨hab,ha.1,hb.1⟩,ha.2,hb.2⟩
      exact hadj.reachable.trans (ih (fun z hz => hp z (List.mem_cons_of_mem _ hz)))
  · rintro ⟨hu,huω,h⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact BlackJoined.refl hu huω
    | tail hxy hyz ih =>
      exact ih.trans (BlackJoined.edge hyz.1.2.1 hyz.1.2.2 hyz.2.1 hyz.2.2 hyz.1.1)

def NecklaceShape.outsideSites (C : NecklaceShape) : Set Site :=
  {v | point v ∉ C.planeDisk ∨ v ∈ C.vertices}

def NecklaceShape.insideSites (C : NecklaceShape) : Set Site := point ⁻¹' C.planeDisk

theorem NecklaceShape.boundary_sites (C : NecklaceShape) :
    C.outsideSites ∩ C.insideSites = (C.vertices : Set Site) := by
  ext v
  constructor
  · rintro ⟨h,hv⟩
    exact h.resolve_left (not_not.mpr hv)
  · intro hv
    exact ⟨Or.inr hv,Or.inl ((C.point_mem_planeTrace_iff v).mpr hv)⟩

def NecklaceShape.quadExteriorGraph (C : NecklaceShape) (Q : GraphQuad) (ω : Configuration) :
    SimpleGraph Site := Necklace.monochromeGraph (C.outsideGraph ⊓ Q.domainGraph) ω true

theorem NecklaceShape.quad_graph_decomposition (C : NecklaceShape) (Q : GraphQuad)
    (ω : Configuration) (hQ : C.insideSites ⊆ (Q.domain : Set Site)) :
    Q.blackGraph ω = C.quadExteriorGraph Q ω ⊔ Necklace.monochromeGraph C.insideGraph ω true := by
  ext u v
  constructor
  · intro h
    by_cases he : C.insideEdge u v
    · exact Or.inr ⟨⟨h.1.1,he⟩,h.2⟩
    · exact Or.inl ⟨⟨⟨h.1.1,he⟩,h.1⟩,h.2⟩
  · rintro (h | h)
    · exact ⟨h.1.2,h.2⟩
    · have hends := C.insideEdge_endpoints h.1.1 h.1.2
      exact ⟨⟨h.1.1,hQ hends.1,hQ hends.2⟩,h.2⟩

theorem NecklaceShape.quad_exterior_eq (C : NecklaceShape) (Q : GraphQuad)
    {ω η : Configuration} (heq : Set.EqOn ω η C.outsideSites) :
    C.quadExteriorGraph Q ω = C.quadExteriorGraph Q η := by
  ext u v
  have hends : (C.outsideGraph ⊓ Q.domainGraph).Adj u v →
      ω u = η u ∧ ω v = η v := by
    intro h
    have hsites := C.outsideEdge_endpoints h.1.1 h.1.2
    exact ⟨heq hsites.1,heq hsites.2⟩
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor
  · intro h
    exact ⟨h.1,(hends h.1).1.symm.trans h.2.1,(hends h.1).2.symm.trans h.2.2⟩
  · intro h
    exact ⟨h.1,(hends h.1).1.trans h.2.1,(hends h.1).2.trans h.2.2⟩

/-- Correct exterior reading for literal edge-restricted disks. The
exterior graph keeps every exterior chord, even between boundary sites. -/
theorem NecklaceShape.plane_exterior_reachable_iff (C : NecklaceShape) (Q : GraphQuad)
    (hQ : C.insideSites ⊆ (Q.domain : Set Site)) {ω η : Configuration}
    (hω : C.Colored ω) (hη : C.Colored η) (heq : Set.EqOn ω η C.outsideSites)
    (hbit : C.PlaneJoined ω ↔ C.PlaneJoined η)
    {u v : Site} (hu : u ∈ C.outsideSites) (hv : v ∈ C.outsideSites)
    (huω : ω u = true) (hvω : ω v = true) :
    (Q.blackGraph ω).Reachable u v ↔ (Q.blackGraph η).Reachable u v := by
  let exterior : Set Site := {v | v ∈ C.outsideSites ∧ ω v = true}
  let inner : Set Site := {v | v ∈ C.insideSites ∧ ω v = true}
  let inner' : Set Site := {v | v ∈ C.insideSites ∧ η v = true}
  let interior : Set Site := inner ∪ inner'
  rw [C.quad_graph_decomposition Q ω hQ,C.quad_graph_decomposition Q η hQ,
    ← C.quad_exterior_eq Q heq]
  apply Necklace.replace_interior_reachable_iff (C.quadExteriorGraph Q ω)
    (Necklace.monochromeGraph C.insideGraph ω true)
    (Necklace.monochromeGraph C.insideGraph η true) exterior interior
  · intro x y h
    have hs := C.outsideEdge_endpoints h.1.1.1 h.1.1.2
    exact ⟨⟨hs.1,h.2.1⟩,⟨hs.2,h.2.2⟩⟩
  · intro x y h
    have hs := C.insideEdge_endpoints h.1.1 h.1.2
    exact ⟨Or.inl ⟨hs.1,h.2.1⟩,Or.inl ⟨hs.2,h.2.2⟩⟩
  · intro x y h
    have hs := C.insideEdge_endpoints h.1.1 h.1.2
    exact ⟨Or.inr ⟨hs.1,h.2.1⟩,Or.inr ⟨hs.2,h.2.2⟩⟩
  · intro x hx y hy
    have hxI : x ∈ C.insideSites := hx.2.elim And.left And.left
    have hyI : y ∈ C.insideSites := hy.2.elim And.left And.left
    have hxC : x ∈ C.vertices := by
      change x ∈ (C.vertices : Set Site)
      rw [← C.boundary_sites]
      exact ⟨hx.1.1,hxI⟩
    have hyC : y ∈ C.vertices := by
      change y ∈ (C.vertices : Set Site)
      rw [← C.boundary_sites]
      exact ⟨hy.1.1,hyI⟩
    exact ⟨C.plane_boundary_transport hω hη hbit.mp hxC hyC hx.1.2 hy.1.2,
      C.plane_boundary_transport hη hω hbit.mpr hxC hyC
        ((heq hx.1.1).symm.trans hx.1.2) ((heq hy.1.1).symm.trans hy.1.2)⟩
  · exact ⟨hu,huω⟩
  · exact ⟨hv,hvω⟩

theorem NecklaceShape.plane_crossing_iff (C : NecklaceShape) (Q : GraphQuad)
    (hQ : C.insideSites ⊆ (Q.domain : Set Site))
    (hfirst : (Q.firstSide : Set Site) ⊆ C.outsideSites)
    (hsecond : (Q.secondSide : Set Site) ⊆ C.outsideSites)
    {ω η : Configuration} (hω : C.Colored ω) (hη : C.Colored η)
    (heq : Set.EqOn ω η C.outsideSites) (hbit : C.PlaneJoined ω ↔ C.PlaneJoined η) :
    Q.Crossing ω ↔ Q.Crossing η := by
  have forward {a b : Configuration} (ha : C.Colored a) (hb : C.Colored b)
      (hab : Set.EqOn a b C.outsideSites) (hbits : C.PlaneJoined a ↔ C.PlaneJoined b)
      (hc : Q.Crossing a) : Q.Crossing b := by
    obtain ⟨u,hu,v,hv,p,hp⟩ := hc
    have hj : BlackJoined Q.domain a u v := ⟨p,hp⟩
    obtain ⟨huQ,huω,hr⟩ := (Q.blackJoined_iff a u v).mp hj
    have hvω := (hp v p.end_mem_support).2
    have hr' := (C.plane_exterior_reachable_iff Q hQ ha hb hab hbits
      (hfirst hu) (hsecond hv) huω hvω).mp hr
    obtain ⟨q,hq⟩ := (Q.blackJoined_iff b u v).mpr
      ⟨huQ,(hab (hfirst hu)).symm.trans huω,hr'⟩
    exact ⟨u,hu,v,hv,q,hq⟩
  exact ⟨forward hω hη heq hbit,forward hη hω heq.symm hbit.symm⟩

#print axioms NecklaceShape.plane_boundary_transport
#print axioms NecklaceShape.quad_graph_decomposition
#print axioms NecklaceShape.plane_exterior_reachable_iff
#print axioms NecklaceShape.plane_crossing_iff

end ExceptionalTimes.PairSquareSewing
