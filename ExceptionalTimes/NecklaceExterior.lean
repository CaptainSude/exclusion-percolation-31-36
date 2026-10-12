import ExceptionalTimes.NecklaceGeometry

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

theorem BlackJoined.refl {D : Finset Site} {ω : Configuration} {u : Site}
    (hu : u ∈ D) (hω : ω u = true) : BlackJoined D ω u u := by
  refine ⟨SimpleGraph.Walk.nil,?_⟩
  intro z hz
  have hzu : z = u := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
  simpa only [hzu] using And.intro hu hω

theorem BlackJoined.edge {D : Finset Site} {ω : Configuration} {u v : Site}
    (hu : u ∈ D) (hv : v ∈ D) (huω : ω u = true) (hvω : ω v = true)
    (h : TriangularAdj u v) : BlackJoined D ω u v := by
  refine ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil,?_⟩
  intro z hz
  change z ∈ [u,v] at hz
  have hz' : z = u ∨ z = v := by simpa using hz
  rcases hz' with rfl | rfl
  · exact ⟨hu,huω⟩
  · exact ⟨hv,hvω⟩

theorem NecklaceShape.black_mem_runs (C : NecklaceShape) {ω : Configuration}
    (hω : C.Colored ω) {u : Site} (hu : u ∈ C.vertices) (huω : ω u = true) :
    u ∈ (C.run 0).support ∨ u ∈ (C.run 2).support := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hu
  have hi' := List.mem_toFinset.mp hi
  have hc := (hω i u hi').symm.trans huω
  fin_cases i
  · exact Or.inl hi'
  · simp at hc
  · exact Or.inr hi'
  · simp at hc

theorem NecklaceShape.black_run_joined (C : NecklaceShape) (Λ : Finset Site)
    (hC : C.vertices ⊆ Λ) {ω : Configuration} (hω : C.Colored ω)
    (i : Fin 4) (hi : i.val % 2 = 0) {u v : Site}
    (hu : u ∈ (C.run i).support) (hv : v ∈ (C.run i).support) :
    BlackJoined (C.filled Λ) ω u v := by
  apply blackJoined_along_walk (C.run i) _ hu hv
  intro z hz
  refine ⟨C.vertices_subset_filled Λ hC (C.run_mem_vertices i hz),?_⟩
  simpa only [hi,decide_true] using hω i z hz

theorem NecklaceShape.join_connects_runs (C : NecklaceShape) (Λ : Finset Site)
    (hC : C.vertices ⊆ Λ) {ω : Configuration} (hω : C.Colored ω)
    (hjoin : (C.joinQuad Λ).Crossing ω) {u v : Site}
    (hu : u ∈ (C.run 0).support) (hv : v ∈ (C.run 2).support) :
    BlackJoined (C.filled Λ) ω u v := by
  obtain ⟨a,ha,b,hb,p,hp⟩ := hjoin
  exact ((C.black_run_joined Λ hC hω 0 rfl hu (List.mem_toFinset.mp ha)).trans
    ⟨p,hp⟩).trans (C.black_run_joined Λ hC hω 2 rfl (List.mem_toFinset.mp hb) hv)

/-- Every same-color boundary connectivity is determined by the one
black-join bit. This is a graph theorem, with no planar separation input. -/
theorem NecklaceShape.boundary_join_transport (C : NecklaceShape) (Λ : Finset Site)
    (hC : C.vertices ⊆ Λ) {ω η : Configuration} (hω : C.Colored ω) (hη : C.Colored η)
    (hjoin : (C.joinQuad Λ).Crossing ω → (C.joinQuad Λ).Crossing η)
    {u v : Site} (hu : u ∈ C.vertices) (hv : v ∈ C.vertices)
    (h : BlackJoined (C.filled Λ) ω u v) : BlackJoined (C.filled Λ) η u v := by
  obtain ⟨p,hp⟩ := h
  have huω := (hp u p.start_mem_support).2
  have hvω := (hp v p.end_mem_support).2
  rcases C.black_mem_runs hω hu huω with hu0 | hu2 <;>
    rcases C.black_mem_runs hω hv hvω with hv0 | hv2
  · exact C.black_run_joined Λ hC hη 0 rfl hu0 hv0
  · exact C.join_connects_runs Λ hC hη
      (hjoin ⟨u,List.mem_toFinset.mpr hu0,v,List.mem_toFinset.mpr hv2,p,hp⟩) hu0 hv2
  · have hrev : BlackJoined (C.filled Λ) ω v u := BlackJoined.symm ⟨p,hp⟩
    obtain ⟨q,hq⟩ := hrev
    exact (C.join_connects_runs Λ hC hη
      (hjoin ⟨v,List.mem_toFinset.mpr hv0,u,List.mem_toFinset.mpr hu2,q,hq⟩) hv0 hu2).symm
  · exact C.black_run_joined Λ hC hη 2 rfl hu2 hv2

theorem walk_preserves {D : Finset Site} {ω : Configuration} (P : Site → Prop)
    (hstep : ∀ u v, TriangularAdj u v → u ∈ D → v ∈ D →
      ω u = true → ω v = true → P u → P v)
    {u v : Site} (p : triangularGraph.Walk u v)
    (hp : ∀ z ∈ p.support, z ∈ D ∧ ω z = true) (hu : P u) : P v := by
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih =>
    have ha := hp a (List.mem_cons_self ..)
    have htail : ∀ z ∈ p.support, z ∈ D ∧ ω z = true :=
      fun z hz => hp z (List.mem_cons_of_mem _ hz)
    have hb := htail b p.start_mem_support
    exact ih htail (hstep a b hab ha.1 hb.1 ha.2 hb.2 hu)

/-- A walk entering a cut region can be replaced using only the
connectivity of its boundary. All replacement walks remain in the quad. -/
theorem blackJoined_transport_across_cut (D B E : Finset Site)
    (hDE : D ⊆ E)
    (hcut : ∀ u v, u ∈ D → v ∉ D → TriangularAdj u v → u ∈ B)
    {ω η : Configuration}
    (heq : ∀ v, v ∉ D ∨ v ∈ B → ω v = η v)
    (hboundary : ∀ u ∈ B, ∀ v ∈ B, BlackJoined D ω u v → BlackJoined D η u v)
    {s t : Site} (hs : s ∉ D) (ht : t ∉ D)
    (h : BlackJoined E ω s t) : BlackJoined E η s t := by
  let P : Site → Prop := fun v =>
    (v ∉ D ∧ BlackJoined E η s v) ∨
      (v ∈ D ∧ ∃ w ∈ B, BlackJoined E η s w ∧ BlackJoined D ω w v)
  have hstep : ∀ u v, TriangularAdj u v → u ∈ E → v ∈ E →
      ω u = true → ω v = true → P u → P v := by
    intro u v huv huE hvE huω hvω hPu
    rcases hPu with ⟨huD,hjoin⟩ | ⟨huD,w,hw,hjoin,hlocal⟩
    · by_cases hvD : v ∈ D
      · have hvB := hcut v u hvD huD (triangularGraph.adj_symm huv)
        have hedge : BlackJoined E η u v := BlackJoined.edge huE hvE
          ((heq u (Or.inl huD)).symm.trans huω) ((heq v (Or.inr hvB)).symm.trans hvω) huv
        exact Or.inr ⟨hvD,v,hvB,hjoin.trans hedge,BlackJoined.refl hvD hvω⟩
      · exact Or.inl ⟨hvD,hjoin.trans (BlackJoined.edge huE hvE
          ((heq u (Or.inl huD)).symm.trans huω) ((heq v (Or.inl hvD)).symm.trans hvω) huv)⟩
    · by_cases hvD : v ∈ D
      · exact Or.inr ⟨hvD,w,hw,hjoin,hlocal.trans (BlackJoined.edge huD hvD huω hvω huv)⟩
      · have huB := hcut u v huD hvD huv
        have hwu := (hboundary w hw u huB hlocal).mono hDE
        exact Or.inl ⟨hvD,(hjoin.trans hwu).trans (BlackJoined.edge huE hvE
          ((heq u (Or.inr huB)).symm.trans huω) ((heq v (Or.inl hvD)).symm.trans hvω) huv)⟩
  obtain ⟨p,hp⟩ := h
  have hsE := (hp s p.start_mem_support).1
  have hsω := (hp s p.start_mem_support).2
  have hPs : P s := Or.inl ⟨hs,BlackJoined.refl hsE ((heq s (Or.inl hs)).symm.trans hsω)⟩
  rcases walk_preserves P hstep p hp hPs with ⟨_,htransport⟩ | ⟨htD,_⟩
  · exact htransport
  · exact False.elim (ht htD)

/-- Literal exterior crossing dependence at an actual necklace: the
entire filled region lies in the quad, both terminal sets lie outside it,
and the two environments have identical exterior bits and join bits. -/
theorem NecklaceShape.crossing_iff_of_join_iff (C : NecklaceShape) (Λ : Finset Site)
    (Q : GraphQuad) (hC : C.vertices ⊆ Λ) (hDQ : C.filled Λ ⊆ Q.domain)
    (hfirst : Disjoint Q.firstSide (C.filled Λ))
    (hsecond : Disjoint Q.secondSide (C.filled Λ))
    {ω η : Configuration} (hω : C.Colored ω) (hη : C.Colored η)
    (hext : ∀ v, v ∉ C.filled Λ → ω v = η v)
    (hjoin : (C.joinQuad Λ).Crossing ω ↔ (C.joinQuad Λ).Crossing η) :
    Q.Crossing ω ↔ Q.Crossing η := by
  have hboundaryEq : ∀ v ∈ C.vertices, ω v = η v := by
    intro v hv
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
    exact (hω i v (List.mem_toFinset.mp hi)).trans (hη i v (List.mem_toFinset.mp hi)).symm
  have heq : ∀ v, v ∉ C.filled Λ ∨ v ∈ C.vertices → ω v = η v := by
    intro v hv
    exact hv.elim (hext v) (hboundaryEq v)
  have forward {a b : Configuration} (h : ∀ v, v ∉ C.filled Λ ∨ v ∈ C.vertices → a v = b v)
      (hbd : ∀ u ∈ C.vertices, ∀ v ∈ C.vertices,
        BlackJoined (C.filled Λ) a u v → BlackJoined (C.filled Λ) b u v)
      (ha : Q.Crossing a) : Q.Crossing b := by
    obtain ⟨s,hs,t,ht,p,hp⟩ := ha
    have hsD : s ∉ C.filled Λ := fun h => Finset.disjoint_left.mp hfirst hs h
    have htD : t ∉ C.filled Λ := fun h => Finset.disjoint_left.mp hsecond ht h
    obtain ⟨q,hq⟩ := blackJoined_transport_across_cut (C.filled Λ) C.vertices Q.domain hDQ
      (fun u v hu hv huv => C.edge_exits_on_cycle Λ hC hu hv huv) h hbd hsD htD ⟨p,hp⟩
    exact ⟨s,hs,t,ht,q,hq⟩
  exact ⟨forward heq (fun _ hu _ hv h => C.boundary_join_transport Λ hC hω hη hjoin.mp hu hv h),
    forward (fun v hv => (heq v hv).symm)
      (fun _ hu _ hv h => C.boundary_join_transport Λ hC hη hω hjoin.mpr hu hv h)⟩

theorem NecklaceShape.test_eq_of_join_test_eq (C : NecklaceShape) (Λ : Finset Site)
    (Q : GraphQuad) (hC : C.vertices ⊆ Λ) (hDQ : C.filled Λ ⊆ Q.domain)
    (hfirst : Disjoint Q.firstSide (C.filled Λ))
    (hsecond : Disjoint Q.secondSide (C.filled Λ))
    {ω η : Configuration} (hω : C.Colored ω) (hη : C.Colored η)
    (hext : ∀ v, v ∉ C.filled Λ → ω v = η v)
    (hjoin : (C.joinQuad Λ).test ω = (C.joinQuad Λ).test η) : Q.test ω = Q.test η := by
  have hjoin' : (C.joinQuad Λ).Crossing ω ↔ (C.joinQuad Λ).Crossing η :=
    decide_eq_decide.mp hjoin
  exact decide_eq_decide.mpr (C.crossing_iff_of_join_iff Λ Q hC hDQ hfirst hsecond hω hη hext hjoin')

/-- The previously abstract dependence predicate is now discharged by
the actual outer necklace cut. Bit transmission is the sole remaining
input here; no crossing factorization is assumed. -/
theorem necklaceCrossingDependence_of_outer_necklace
    {I : Type*} (quads : I → GraphQuad) (C : NecklaceShape) (Λ D : Finset Site)
    (x z : Site) (A B : TwoTimeConfiguration) (φ : DimerBinaryResponse.Table) (ψ : Bool → Bool)
    (hC : C.vertices ⊆ Λ)
    (hDQ : ∀ q, C.filled Λ ⊆ (quads q).domain)
    (hfirst : ∀ q, Disjoint (quads q).firstSide (C.filled Λ))
    (hsecond : ∀ q, Disjoint (quads q).secondSide (C.filled Λ))
    (hcolored : ∀ t a, C.Colored (annotationConfiguration D x z A B t a))
    (hext : ∀ t a b v, v ∉ C.filled Λ →
      annotationConfiguration D x z A B t a v = annotationConfiguration D x z A B t b v)
    (hbit : ∀ t a, (C.joinQuad Λ).test (annotationConfiguration D x z A B t a) =
      annotationBit φ ψ a) : NecklaceCrossingDependence quads D x z A B φ ψ := by
  intro q t a b hab
  apply C.test_eq_of_join_test_eq Λ (quads q) hC (hDQ q) (hfirst q) (hsecond q)
    (hcolored t a) (hcolored t b) (hext t a b)
  exact (hbit t a).trans (hab.trans (hbit t b).symm)

#print axioms NecklaceShape.boundary_join_transport
#print axioms blackJoined_transport_across_cut
#print axioms NecklaceShape.crossing_iff_of_join_iff
#print axioms necklaceCrossingDependence_of_outer_necklace

end ExceptionalTimes.PairSquareSewing
