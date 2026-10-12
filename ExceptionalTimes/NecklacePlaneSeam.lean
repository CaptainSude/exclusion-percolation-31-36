import ExceptionalTimes.NecklacePlaneTransmission

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open TriangularPlane

theorem NecklaceShape.disk_monochrome_reachable (C : NecklaceShape) (ω : Configuration)
    (color : Bool) {a b : Site} (p : triangularGraph.Walk a b)
    (hp : walkTrace p ⊆ C.planeDisk) (hc : ∀ z ∈ p.support, ω z = color) :
    (Necklace.monochromeGraph C.insideGraph ω color).Reachable a b := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have hmid : edgePoint a b (1/2) ∈ C.planeDisk :=
      hp (Or.inl ⟨1/2,by norm_num,by norm_num,rfl⟩)
    have hab' : (Necklace.monochromeGraph C.insideGraph ω color).Adj a b :=
      ⟨⟨hab,hmid⟩,hc a (List.mem_cons_self ..),
        hc b (List.mem_cons_of_mem _ p.start_mem_support)⟩
    exact hab'.reachable.trans (ih (fun _ h => hp (Or.inr h))
      (fun z hz => hc z (List.mem_cons_of_mem _ hz)))

theorem NecklaceShape.insideGraph_mono {C D : NecklaceShape} (h : C.planeDisk ⊆ D.planeDisk) :
    C.insideGraph ≤ D.insideGraph := by
  intro u v huv
  exact ⟨huv.1,h huv.2⟩

/-- Literal source connections, now in the correct edge-restricted
outer disk. The entire drawn paths are required to stay in that disk. -/
def PlaneNecklaceConnections (C D : NecklaceShape) (support : Finset Site) (ω : Configuration) : Prop :=
  ∃ start finish : Fin 4 → Site,
    ∃ path : ∀ i, triangularGraph.Walk (start i) (finish i),
      (∀ i, start i ∈ (C.run i).support ∧ finish i ∈ (D.run i).support) ∧
      (∀ i, (path i).IsPath) ∧
      (∀ i, walkTrace (path i) ⊆ D.planeDisk) ∧
      (∀ i v, v ∈ (path i).support → v ∈ support ∧ ω v = decide (i.val % 2 = 0)) ∧
      (∀ i j, i ≠ j → List.Disjoint (path i).support (path j).support)

/-- Any prescribed same-color join propagates along the corresponding
two actual connector paths in the geometric outer disk. -/
theorem plane_necklace_join_propagates {C D : NecklaceShape} {support : Finset Site}
    {ω : Configuration} (hCD : C.planeDisk ⊆ D.planeDisk)
    (hCω : C.Colored ω) (hDω : D.Colored ω)
    (hconn : PlaneNecklaceConnections C D support ω)
    (i j : Fin 4) (color : Bool)
    (hi : decide (i.val % 2 = 0) = color) (hj : decide (j.val % 2 = 0) = color)
    (hjoin : (Necklace.monochromeGraph C.insideGraph ω color).Reachable (C.start i) (C.start j)) :
    (Necklace.monochromeGraph D.insideGraph ω color).Reachable (D.start i) (D.start j) := by
  obtain ⟨s,t,p,he,_,hdisk,hc,_⟩ := hconn
  have hmono : Necklace.monochromeGraph C.insideGraph ω color ≤
      Necklace.monochromeGraph D.insideGraph ω color := by
    intro u v h
    exact ⟨NecklaceShape.insideGraph_mono hCD h.1,h.2⟩
  have Cpath (k : Fin 4) (hk : decide (k.val % 2 = 0) = color) :
      (Necklace.monochromeGraph D.insideGraph ω color).Reachable (C.start k) (s k) := by
    have h := C.run_vertices_reachable_inside hCω k (C.run k).start_mem_support (he k).1
    rw [hk] at h
    exact h.mono hmono
  have Dpath (k : Fin 4) (hk : decide (k.val % 2 = 0) = color) :
      (Necklace.monochromeGraph D.insideGraph ω color).Reachable (D.start k) (t k) := by
    have h := D.run_vertices_reachable_inside hDω k (D.run k).start_mem_support (he k).2
    rwa [hk] at h
  have connector (k : Fin 4) (hk : decide (k.val % 2 = 0) = color) :
      (Necklace.monochromeGraph D.insideGraph ω color).Reachable (s k) (t k) :=
    D.disk_monochrome_reachable ω color (p k) (hdisk k) (fun z hz => (hc k z hz).2.trans hk)
  exact ((((((Dpath i hi).trans (connector i hi).symm).trans (Cpath i hi).symm).trans
    (hjoin.mono hmono)).trans (Cpath j hj)).trans (connector j hj)).trans (Dpath j hj).symm

def NecklaceShape.PlaneWhiteJoined (C : NecklaceShape) (ω : Configuration) : Prop :=
  (Necklace.monochromeGraph C.insideGraph ω false).Reachable (C.start 1) (C.start 3)

theorem plane_black_join_propagates {C D : NecklaceShape} {support : Finset Site}
    {ω : Configuration} (hCD : C.planeDisk ⊆ D.planeDisk)
    (hCω : C.Colored ω) (hDω : D.Colored ω)
    (hconn : PlaneNecklaceConnections C D support ω) : C.PlaneJoined ω → D.PlaneJoined ω :=
  plane_necklace_join_propagates hCD hCω hDω hconn 0 2 true rfl rfl

theorem plane_white_join_propagates {C D : NecklaceShape} {support : Finset Site}
    {ω : Configuration} (hCD : C.planeDisk ⊆ D.planeDisk)
    (hCω : C.Colored ω) (hDω : D.Colored ω)
    (hconn : PlaneNecklaceConnections C D support ω) : C.PlaneWhiteJoined ω → D.PlaneWhiteJoined ω :=
  plane_necklace_join_propagates hCD hCω hDω hconn 1 3 false rfl rfl

theorem planeNecklaceConnections_congr (C D : NecklaceShape) (support : Finset Site)
    {ω η : Configuration} (h : Set.EqOn ω η (support : Set Site)) :
    PlaneNecklaceConnections C D support ω ↔ PlaneNecklaceConnections C D support η := by
  have forward {a b : Configuration} (hab : Set.EqOn a b (support : Set Site))
      (ha : PlaneNecklaceConnections C D support a) : PlaneNecklaceConnections C D support b := by
    obtain ⟨s,t,p,he,hs,hd,hc,hdis⟩ := ha
    refine ⟨s,t,p,he,hs,hd,?_,hdis⟩
    intro i v hv
    exact ⟨(hc i v hv).1,(hab (hc i v hv).1).symm.trans (hc i v hv).2⟩
  exact ⟨forward h,forward h.symm⟩

/-- The geometric all-four relation uses the source sleeves, a screened
pocket, nested actual planar disks, and actual disjoint connector paths.
Its color requirements depend only on the displayed finite support. -/
def PlaneNecklaceSeamRelation {Λ : Finset Site}
    (support innerSleeve outerSleeve pocket : Finset Site)
    (C D : NecklaceShape) (bits : ↥Λ → Bool) : Prop :=
  C.vertices ⊆ innerSleeve ∧ D.vertices ⊆ outerSleeve ∧
  C.vertices ⊆ Λ ∧ D.vertices ⊆ Λ ∧
  (∀ v ∈ pocket, point v ∈ C.planeDisk) ∧ C.planeDisk ⊆ D.planeDisk ∧
  C.Colored (complete bits) ∧ D.Colored (complete bits) ∧
  PlaneNecklaceConnections C D support (complete bits)

theorem planeNecklaceSeamRelation_supported {Λ : Finset Site}
    (support innerSleeve outerSleeve pocket : Finset Site)
    (hin : innerSleeve ⊆ support) (hout : outerSleeve ⊆ support) :
    SupportedSeamRelation support
      (PlaneNecklaceSeamRelation (Λ := Λ) support innerSleeve outerSleeve pocket) := by
  intro C D ω η h
  have heq : Set.EqOn (complete ω) (complete η) (support : Set Site) := by
    intro v hv
    by_cases hΛ : v ∈ Λ
    · simpa [complete,hΛ] using h ⟨v,hΛ⟩ hv
    · simp [complete,hΛ]
  have forward {a b : ↥Λ → Bool} (hab : Set.EqOn (complete a) (complete b) (support : Set Site)) :
      PlaneNecklaceSeamRelation support innerSleeve outerSleeve pocket C D a →
      PlaneNecklaceSeamRelation support innerSleeve outerSleeve pocket C D b := by
    rintro ⟨hCi,hDo,hCΛ,hDΛ,hp,hCD,hCa,hDa,hconn⟩
    exact ⟨hCi,hDo,hCΛ,hDΛ,hp,hCD,
      (C.colored_congr support (hCi.trans hin) hab).mp hCa,
      (D.colored_congr support (hDo.trans hout) hab).mp hDa,
      (planeNecklaceConnections_congr C D support hab).mp hconn⟩
  exact ⟨forward heq,forward heq.symm⟩

noncomputable def planeNecklaceSuccess {Λ : Finset Site}
    (inside support innerSleeve outerSleeve pocket : Finset Site) : Sources Λ → Bool :=
  fourWayTest inside (PlaneNecklaceSeamRelation support innerSleeve outerSleeve pocket)

theorem planeNecklaceSuccess_supported {Λ : Finset Site}
    (inside support innerSleeve outerSleeve pocket : Finset Site)
    (hin : innerSleeve ⊆ support) (hout : outerSleeve ⊆ support) :
    SupportedSourceTest support
      (planeNecklaceSuccess (Λ := Λ) inside support innerSleeve outerSleeve pocket) :=
  fourWayTest_supported support inside _
    (planeNecklaceSeamRelation_supported support innerSleeve outerSleeve pocket hin hout)

theorem planeNecklaceSuccess_seamSwap {Λ : Finset Site}
    (inside support innerSleeve outerSleeve pocket : Finset Site) (ω : Sources Λ) :
    planeNecklaceSuccess inside support innerSleeve outerSleeve pocket (seamSwap inside ω) =
      planeNecklaceSuccess inside support innerSleeve outerSleeve pocket ω :=
  fourWayTest_seamSwap inside _ ω

/-- Named published deterministic input: the finite disk Hex alternative
invoked in 06-sewing.tex, Lemma 6.5, proof beginning "Hex duality in the
disk bounded by the inner necklace" (source commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a).

The necklace is an actual simple embedded lattice cycle (cycle_isCycle
and the proved triangular plane drawing). The graph consists exactly of
lattice edges wholly contained in its actual planar disk, by
insideEdge_iff_whole_edge. Run vertices are included. The classical disk
Hex statement includes the finite-disk interpretation for this literal
simple polygon; this file does not separately prove the Jordan theorem.
This proposition is an explicit theorem parameter, never a global axiom.
It contains no sleeve probability, failure estimate, or sewing error. -/
def PublishedPlaneDiskHex : Prop :=
  ∀ (C : NecklaceShape) (ω : Configuration), C.Colored ω →
    (C.PlaneJoined ω ↔ ¬ C.PlaneWhiteJoined ω)

theorem plane_necklace_join_iff (hexInput : PublishedPlaneDiskHex)
    {C D : NecklaceShape} {support : Finset Site} {ω : Configuration}
    (hCD : C.planeDisk ⊆ D.planeDisk) (hCω : C.Colored ω) (hDω : D.Colored ω)
    (hconn : PlaneNecklaceConnections C D support ω) : C.PlaneJoined ω ↔ D.PlaneJoined ω := by
  constructor
  · exact plane_black_join_propagates hCD hCω hDω hconn
  · intro houter
    by_contra hinner
    have hwhite : C.PlaneWhiteJoined ω := by
      by_contra hn
      exact hinner ((hexInput C ω hCω).mpr hn)
    exact (hexInput D ω hDω).mp houter
      (plane_white_join_propagates hCD hCω hDω hconn hwhite)

theorem plane_necklace_joinBit_eq (hexInput : PublishedPlaneDiskHex)
    {C D : NecklaceShape} {support : Finset Site} {ω : Configuration}
    (hCD : C.planeDisk ⊆ D.planeDisk) (hCω : C.Colored ω) (hDω : D.Colored ω)
    (hconn : PlaneNecklaceConnections C D support ω) : C.planeJoinBit ω = D.planeJoinBit ω :=
  decide_eq_decide.mpr (plane_necklace_join_iff hexInput hCD hCω hDω hconn)

theorem PlaneNecklaceSeamRelation.transmits (hexInput : PublishedPlaneDiskHex)
    {Λ support innerSleeve outerSleeve pocket : Finset Site} {C D : NecklaceShape}
    {bits : ↥Λ → Bool} (h : PlaneNecklaceSeamRelation support innerSleeve outerSleeve pocket C D bits) :
    C.planeJoinBit (complete bits) = D.planeJoinBit (complete bits) := by
  obtain ⟨_,_,_,_,_,hCD,hC,hD,hconn⟩ := h
  exact plane_necklace_joinBit_eq hexInput hCD hC hD hconn

#print axioms plane_necklace_join_propagates
#print axioms plane_black_join_propagates
#print axioms plane_white_join_propagates
#print axioms planeNecklaceSeamRelation_supported
#print axioms planeNecklaceSuccess_seamSwap
#print axioms PlaneNecklaceSeamRelation.transmits

end ExceptionalTimes.PairSquareSewing
