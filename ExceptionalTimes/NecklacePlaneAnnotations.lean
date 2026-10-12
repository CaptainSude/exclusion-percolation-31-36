import ExceptionalTimes.NecklacePlaneSeam

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open DimerBinaryResponse

theorem NecklaceShape.planeJoinBit_congr (C : NecklaceShape) {ω η : Configuration}
    (h : Set.EqOn ω η C.insideSites) : C.planeJoinBit ω = C.planeJoinBit η := by
  have hg : Necklace.monochromeGraph C.insideGraph ω true =
      Necklace.monochromeGraph C.insideGraph η true := by
    ext u v
    have heq : C.insideGraph.Adj u v → ω u = η u ∧ ω v = η v := by
      intro huv
      have hs := C.insideEdge_endpoints huv.1 huv.2
      exact ⟨h hs.1,h hs.2⟩
    constructor
    · intro huv
      exact ⟨huv.1,(heq huv.1).1.symm.trans huv.2.1,(heq huv.1).2.symm.trans huv.2.2⟩
    · intro huv
      exact ⟨huv.1,(heq huv.1).1.trans huv.2.1,(heq huv.1).2.trans huv.2.2⟩
  apply decide_eq_decide.mpr
  change (Necklace.monochromeGraph C.insideGraph ω true).Reachable (C.start 0) (C.start 2) ↔
    (Necklace.monochromeGraph C.insideGraph η true).Reachable (C.start 0) (C.start 2)
  rw [hg]

theorem NecklaceShape.planeJoinBit_mono (C : NecklaceShape) {ω η : Configuration}
    (h : ∀ v, ω v = true → η v = true) :
    C.planeJoinBit ω = true → C.planeJoinBit η = true := by
  intro hj
  have hj' : C.PlaneJoined ω := of_decide_eq_true hj
  apply decide_eq_true
  apply hj'.mono
  intro u v huv
  exact ⟨huv.1,h u huv.2.1,h v huv.2.2⟩

noncomputable def planePairJoinTable (C : NecklaceShape) (ω : Configuration) (x z : Site) :
    DimerBinaryResponse.Table :=
  DimerBinaryResponse.Table.ofFunction (fun u v => C.planeJoinBit (putPair ω x z u v))

@[simp] theorem planePairJoinTable_eval (C : NecklaceShape) (ω : Configuration)
    (x z : Site) (u v : Bool) :
    (planePairJoinTable C ω x z).eval u v = C.planeJoinBit (putPair ω x z u v) :=
  DimerBinaryResponse.Table.eval_ofFunction _ u v

theorem planePairJoinTable_increasing (C : NecklaceShape) (ω : Configuration) (x z : Site) :
    DimerBinaryResponse.Increasing (planePairJoinTable C ω x z) := by
  change (C.planeJoinBit (putPair ω x z false false) = true →
      C.planeJoinBit (putPair ω x z false true) = true) ∧
    (C.planeJoinBit (putPair ω x z false false) = true →
      C.planeJoinBit (putPair ω x z true false) = true) ∧
    (C.planeJoinBit (putPair ω x z false true) = true →
      C.planeJoinBit (putPair ω x z true true) = true) ∧
    (C.planeJoinBit (putPair ω x z true false) = true →
      C.planeJoinBit (putPair ω x z true true) = true)
  exact ⟨C.planeJoinBit_mono (putPair_mono ω x z id (by simp)),
    C.planeJoinBit_mono (putPair_mono ω x z (by simp) id),
    C.planeJoinBit_mono (putPair_mono ω x z (by simp) id),
    C.planeJoinBit_mono (putPair_mono ω x z id (by simp))⟩

noncomputable def planeSquareJoin (C : NecklaceShape) (ω : Configuration) (D : Finset Site)
    (b : Bool) : Bool := C.planeJoinBit (force D ω b)

theorem planeSquareJoin_increasing (C : NecklaceShape) (ω : Configuration) (D : Finset Site) :
    planeSquareJoin C ω D false = true → planeSquareJoin C ω D true = true := by
  apply C.planeJoinBit_mono
  intro v hv
  by_cases hvD : v ∈ D
  · simp [force,hvD]
  · simpa [force,hvD] using hv

def annotationInner (pairInner squareInner : NecklaceShape) : InteriorAnnotation → NecklaceShape :=
  Sum.elim (fun _ => pairInner) (fun _ => squareInner)

theorem annotation_inner_join (pairInner squareInner : NecklaceShape)
    (D : Finset Site) (x z : Site) (A B : TwoTimeConfiguration) (ω η : Configuration)
    (hA : ∀ t, Set.EqOn (A t) ω pairInner.insideSites)
    (hB : ∀ t, Set.EqOn (B t) η squareInner.insideSites)
    (t : Bool) (a : InteriorAnnotation) :
    (annotationInner pairInner squareInner a).planeJoinBit (annotationConfiguration D x z A B t a) =
      annotationBit (planePairJoinTable pairInner ω x z) (planeSquareJoin squareInner η D) a := by
  cases a with
  | inl a =>
    change pairInner.planeJoinBit (putPair (A t) x z a.1 a.2) = _
    rw [pairInner.planeJoinBit_congr (putPair_congr_on _ _ x z _ _ _ (hA t))]
    exact (planePairJoinTable_eval pairInner ω x z a.1 a.2).symm
  | inr b =>
    exact squareInner.planeJoinBit_congr (force_congr_on D _ _ _ _ (hB t))

/-- Actual nested necklaces and the published disk Hex alternative
discharge the one-time crossing-dependence predicate for every inserted
pair/square state. Their interior backgrounds are frozen across time. -/
theorem planeNecklaceDependence_from_connections (hexInput : PublishedPlaneDiskHex)
    {I : Type*} (quads : I → GraphQuad) (pairInner squareInner outer : NecklaceShape)
    (D support : Finset Site) (x z : Site) (A B : TwoTimeConfiguration) (ω η : Configuration)
    (hA : ∀ t, Set.EqOn (A t) ω pairInner.insideSites)
    (hB : ∀ t, Set.EqOn (B t) η squareInner.insideSites)
    (hpair : pairInner.planeDisk ⊆ outer.planeDisk)
    (hsquare : squareInner.planeDisk ⊆ outer.planeDisk)
    (hQ : ∀ q, outer.insideSites ⊆ ((quads q).domain : Set Site))
    (hfirst : ∀ q, ((quads q).firstSide : Set Site) ⊆ outer.outsideSites)
    (hsecond : ∀ q, ((quads q).secondSide : Set Site) ⊆ outer.outsideSites)
    (hinner : ∀ t a, (annotationInner pairInner squareInner a).Colored
      (annotationConfiguration D x z A B t a))
    (houter : ∀ t a, outer.Colored (annotationConfiguration D x z A B t a))
    (hconn : ∀ t a, PlaneNecklaceConnections (annotationInner pairInner squareInner a) outer support
      (annotationConfiguration D x z A B t a))
    (hext : ∀ t a b, Set.EqOn (annotationConfiguration D x z A B t a)
      (annotationConfiguration D x z A B t b) outer.outsideSites) :
    NecklaceCrossingDependence quads D x z A B
      (planePairJoinTable pairInner ω x z) (planeSquareJoin squareInner η D) := by
  have hbit (t : Bool) (a : InteriorAnnotation) :
      outer.planeJoinBit (annotationConfiguration D x z A B t a) =
        annotationBit (planePairJoinTable pairInner ω x z) (planeSquareJoin squareInner η D) a := by
    have hnest : (annotationInner pairInner squareInner a).planeDisk ⊆ outer.planeDisk := by
      cases a
      · exact hpair
      · exact hsquare
    exact (plane_necklace_joinBit_eq hexInput hnest (hinner t a) (houter t a) (hconn t a)).symm.trans
      (annotation_inner_join pairInner squareInner D x z A B ω η hA hB t a)
  intro q t a b hab
  apply decide_eq_decide.mpr
  apply outer.plane_crossing_iff (quads q) (hQ q) (hfirst q) (hsecond q)
    (houter t a) (houter t b) (hext t a b)
  exact decide_eq_decide.mp ((hbit t a).trans (hab.trans (hbit t b).symm))

/-- The signed-response annotations now use the actual plane-disk join
functions. Their monotonicity and the common exterior readings are
derived, not postulated as pair/square error bounds. -/
theorem transmittedAnnotations_of_plane_necklace_dependence
    {QA QB : Type*} (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (D : Finset Site) (x z : Site) (A B A' B' : TwoTimeConfiguration)
    (pairInner squareInner : NecklaceShape) (ω η : Configuration)
    (hA : NecklaceCrossingDependence quadsA D x z A A'
      (planePairJoinTable pairInner ω x z) (planeSquareJoin squareInner η D))
    (hB : NecklaceCrossingDependence quadsB D x z B' B
      (planePairJoinTable pairInner ω x z) (planeSquareJoin squareInner η D)) :
    TransmittedAnnotations D x z A B A' B'
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  obtain ⟨f,hAF,hA'F⟩ := crossing_dependence_transmissions quadsA outerA D x z A A' _ _ hA
  obtain ⟨g,hB'G,hBG⟩ := crossing_dependence_transmissions quadsB outerB D x z B' B _ _ hB
  exact ⟨planePairJoinTable pairInner ω x z,planeSquareJoin squareInner η D,f,g,
    planePairJoinTable_increasing pairInner ω x z,planeSquareJoin_increasing squareInner η D,
    hAF,hBG,hA'F,hB'G⟩

#print axioms planePairJoinTable_increasing
#print axioms annotation_inner_join
#print axioms planeNecklaceDependence_from_connections
#print axioms transmittedAnnotations_of_plane_necklace_dependence

end ExceptionalTimes.PairSquareSewing
