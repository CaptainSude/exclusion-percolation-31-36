import ExceptionalTimes.NecklacePlaneAnnotations
import ExceptionalTimes.CommonSquare
import ExceptionalTimes.NecklaceDiskContainment

/-! Source06 input boundary and the new two-bit application.

The named source is OpenAI, From critical crossings to quenched near-critical
universality in Voronoi percolation (5 October 2026), commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, section 6.

`SourceOneTimeReading` is the ordinary-coloring reading of Lemma 6.5. It
contains neither a pair update law nor a signed expectation. The theorem
below, rather than an imported percolation assumption, applies this reading
to the two-bit pair annotation and to the square annotation.
-/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open DimerBinaryResponse EnvironmentVariance

/-- All success probabilities below refer to this literal four-way
plane-necklace event. The sets are the source's finite buffered supports;
their physical circular/annular placement is a separate admissibility
certificate, never inferred from their names. -/
structure SourceSeamLayout where
  inside : Finset Site
  support : Finset Site
  innerSleeve : Finset Site
  outerSleeve : Finset Site
  pocket : Finset Site
  inner_supported : innerSleeve ⊆ support
  outer_supported : outerSleeve ⊆ support
  pocket_inside : pocket ⊆ inside
  pocket_disjoint : Disjoint pocket support

def SourceSeamLayout.relation {Λ : Finset Site} (J : SourceSeamLayout)
    (C D : NecklaceShape) (bits : ↥Λ → Bool) : Prop :=
  PlaneNecklaceSeamRelation J.support J.innerSleeve J.outerSleeve J.pocket C D bits ∧
  C.insideSites ⊆ (J.inside : Set Site) ∧
  (J.inside : Set Site) ⊆ D.insideSites ∧ Disjoint D.vertices J.inside

theorem SourceSeamLayout.relation_supported {Λ : Finset Site} (J : SourceSeamLayout) :
    SupportedSeamRelation J.support (J.relation (Λ := Λ)) := by
  intro C D ω η h
  unfold relation
  rw [planeNecklaceSeamRelation_supported J.support J.innerSleeve J.outerSleeve J.pocket
    J.inner_supported J.outer_supported C D ω η h]

noncomputable def SourceSeamLayout.success {Λ : Finset Site}
    (J : SourceSeamLayout) : Sources Λ → Bool :=
  fourWayTest J.inside J.relation

/-- The additional certificates are literal inside/seam placement from
the source's screened sleeves. Forgetting them gives exactly the existing
PlaneNecklaceSuccess event, so no alternative run-intersection event is used. -/
theorem SourceSeamLayout.success_implies_plane {Λ : Finset Site} (J : SourceSeamLayout)
    (ω : Sources Λ) (h : J.success ω=true) :
    planeNecklaceSuccess J.inside J.support J.innerSleeve J.outerSleeve J.pocket ω=true := by
  have h' : FourWaySuccess J.inside J.relation ω := of_decide_eq_true h
  obtain ⟨C,D,hCD⟩ := h'
  apply decide_eq_true
  exact ⟨C,D,fun a b => (hCD a b).1⟩

theorem SourceSeamLayout.success_supported {Λ : Finset Site} (J : SourceSeamLayout) :
    SupportedSourceTest J.support (J.success (Λ := Λ)) :=
  fourWayTest_supported _ _ _ J.relation_supported

theorem SourceSeamLayout.success_swap {Λ : Finset Site} (J : SourceSeamLayout)
    (ω : Sources Λ) : J.success ω.swap=J.success ω :=
  fourWayTest_sourceSwap _ _ _

theorem SourceSeamLayout.success_inside_swap {Λ : Finset Site} (J : SourceSeamLayout)
    (ω : Sources Λ) : J.success (seamSwap J.inside ω)=J.success ω :=
  fourWayTest_seamSwap _ _ ω

/-- Literal physical circular cut, including its deterministic choice of
the closed side for seam sites. This predicate is required when matching a
layout to source06's circular exchange. -/
def SourceSeamLayout.Circular (J : SourceSeamLayout) (Λ : Finset Site)
    (mesh : ℝ) (center : Site) (radius : ℝ) : Prop :=
  0 < radius ∧ J.inside=Λ.filter (fun v =>
    dist (position mesh v) (position mesh center) ≤ radius)

/-- The ordinary one-time reading supplied by source Lemma 6.5, in one
fixed exterior. Either source interior may supply the bit. Other exterior
histories may be fixed arbitrarily, separately at each observed time.

This predicate must be obtained from an actual successful seam with the
source containment/disjointness conditions on its tested quads. It is not
asserted for arbitrary layouts, graph quads, or choices of necklaces. -/
def SourceOneTimeReading {Q : Type*} (quads : Q → GraphQuad)
    (pocket : Finset Site) (inner : Bool → NecklaceShape)
    (background : Bool → TwoTimeConfiguration) : Prop :=
  ∀ q t a b ξ η,
    Set.EqOn ξ (background a t) (pocket : Set Site)ᶜ →
    Set.EqOn η (background b t) (pocket : Set Site)ᶜ →
    (inner a).planeJoinBit ξ=(inner b).planeJoinBit η →
    (quads q).test ξ=(quads q).test η

/-- For the actual source-necklace witnesses, the ordinary reading is
derived using the already formalized literal disk Hex theorem and exterior
path replacement. Changing an arbitrary collection of colors in the pocket
does not affect the necklace runs or connectors. -/
theorem source_one_time_reading_of_relation (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {Q : Type*} (J : SourceSeamLayout) (quads : Q → GraphQuad)
    (ω : Sources Λ) (exterior : Bool) (inner : Bool → NecklaceShape)
    (outer : NecklaceShape) (background : Bool → TwoTimeConfiguration)
    (hrel : ∀ a, J.relation (inner a) outer (sewnField J.inside ω a exterior))
    (hbackground : ∀ a t, Set.EqOn (background a t)
      (complete (sewnField J.inside ω a exterior)) (J.support : Set Site))
    (hext : ∀ a b t, Set.EqOn (background a t) (background b t) outer.outsideSites)
    (hQ : ∀ q, outer.insideSites ⊆ ((quads q).domain : Set Site))
    (hfirst : ∀ q, ((quads q).firstSide : Set Site) ⊆ outer.outsideSites)
    (hsecond : ∀ q, ((quads q).secondSide : Set Site) ⊆ outer.outsideSites) :
    SourceOneTimeReading quads J.pocket inner background := by
  have transfer (a t : Bool) (ξ : Configuration)
      (hξ : Set.EqOn ξ (background a t) (J.pocket : Set Site)ᶜ) :
      (inner a).Colored ξ ∧ outer.Colored ξ ∧
        PlaneNecklaceConnections (inner a) outer J.support ξ ∧
        (inner a).planeDisk ⊆ outer.planeDisk := by
    obtain ⟨⟨hCi,hDo,_,_,_,hCD,hC,hD,hconn⟩,_,_,_⟩ := hrel a
    have heq : Set.EqOn ξ (complete (sewnField J.inside ω a exterior))
        (J.support : Set Site) := by
      intro v hv
      have hvp : v ∉ J.pocket := fun hp => Finset.disjoint_left.mp J.pocket_disjoint hp hv
      exact (hξ hvp).trans (hbackground a t hv)
    exact ⟨((inner a).colored_congr J.support (hCi.trans J.inner_supported) heq).mpr hC,
      (outer.colored_congr J.support (hDo.trans J.outer_supported) heq).mpr hD,
      (planeNecklaceConnections_congr _ _ J.support heq).mpr hconn,hCD⟩
  have hpocket : ∀ v ∈ outer.outsideSites, v ∉ J.pocket := by
    intro v hv hp
    have hin : v ∈ J.inside := J.pocket_inside hp
    rcases hv with hv | hv
    · exact hv ((hrel false).2.2.1 hin)
    · exact Finset.disjoint_left.mp (hrel false).2.2.2 hv hin
  intro q t a b ξ η hξ hη hbit
  obtain ⟨hCξ,hDξ,hconnξ,hnestξ⟩ := transfer a t ξ hξ
  obtain ⟨hCη,hDη,hconnη,hnestη⟩ := transfer b t η hη
  have hbits : outer.planeJoinBit ξ=outer.planeJoinBit η :=
    (plane_necklace_joinBit_eq hexInput hnestξ hCξ hDξ hconnξ).symm.trans
      (hbit.trans (plane_necklace_joinBit_eq hexInput hnestη hCη hDη hconnη))
  apply decide_eq_decide.mpr
  apply outer.plane_crossing_iff (quads q) (hQ q) (hfirst q) (hsecond q) hDξ hDη
  · intro v hv
    exact (hξ (hpocket v hv)).trans ((hext a b t hv).trans (hη (hpocket v hv)).symm)
  · exact decide_eq_decide.mp hbits

def annotationSource : InteriorAnnotation → Bool :=
  Sum.elim (fun _ => false) (fun _ => true)

theorem annotation_agrees_outside_pocket (pocket D : Finset Site) (x z : Site)
    (hx : x ∈ pocket) (hz : x+z ∈ pocket) (hD : D ⊆ pocket)
    (background : Bool → TwoTimeConfiguration) (t : Bool) (a : InteriorAnnotation) :
    Set.EqOn (annotationConfiguration D x z (background false) (background true) t a)
      (background (annotationSource a) t) (pocket : Set Site)ᶜ := by
  intro v hv
  have hv' : v ∉ pocket := hv
  cases a with
  | inl a =>
    exact putPair_outside _ x z v a.1 a.2 (fun he => hv' (he ▸ hx))
      (fun he => hv' (he ▸ hz))
  | inr b =>
    change force D _ b v=_
    simp only [force,ite_eq_right (fun h => hv' (hD h))]
    rfl

/-- The actual two-bit join table is obtained by inserting the two colors
in the actual planar disk. No six-state or local-model universality theorem
is invoked in this conversion of the source's one-time reading. -/
theorem source_reading_pair_square_dependence {Q : Type*} (quads : Q → GraphQuad)
    (pocket D : Finset Site) (x z : Site)
    (hx : x ∈ pocket) (hz : x+z ∈ pocket) (hD : D ⊆ pocket)
    (inner : Bool → NecklaceShape) (background : Bool → TwoTimeConfiguration)
    (raw : Bool → Configuration)
    (hfrozen : ∀ a t, Set.EqOn (background a t) (raw a) (inner a).insideSites)
    (hread : SourceOneTimeReading quads pocket inner background) :
    NecklaceCrossingDependence quads D x z (background false) (background true)
      (planePairJoinTable (inner false) (raw false) x z)
      (planeSquareJoin (inner true) (raw true) D) := by
  intro q t a b hab
  apply hread q t (annotationSource a) (annotationSource b)
    (annotationConfiguration D x z (background false) (background true) t a)
    (annotationConfiguration D x z (background false) (background true) t b)
    (annotation_agrees_outside_pocket pocket D x z hx hz hD background t a)
    (annotation_agrees_outside_pocket pocket D x z hx hz hD background t b)
  have hjoin (c : InteriorAnnotation) := annotation_inner_join (inner false) (inner true)
    D x z (background false) (background true) (raw false) (raw true)
    (hfrozen false) (hfrozen true) t c
  have hinner (c : InteriorAnnotation) :
      inner (annotationSource c)=annotationInner (inner false) (inner true) c := by
    cases c <;> rfl
  rw [hinner a,hinner b,hjoin a,hjoin b]
  exact hab

/-- Two ordinary source readings give the four transmitted evaluations
used by the checked signed exchange theorem. All pair-specific content is
proved here from local overwrites and the finite monotone truth table. -/
theorem source_readings_transmitted {QA QB : Type*}
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (pocket D : Finset Site) (x z : Site)
    (hx : x ∈ pocket) (hz : x+z ∈ pocket) (hD : D ⊆ pocket)
    (inner : Bool → NecklaceShape) (raw : Bool → Configuration)
    (A B A' B' : TwoTimeConfiguration)
    (hfreezeA : ∀ t, Set.EqOn (A t) (raw false) (inner false).insideSites)
    (hfreezeB : ∀ t, Set.EqOn (B t) (raw true) (inner true).insideSites)
    (hfreezeA' : ∀ t, Set.EqOn (A' t) (raw true) (inner true).insideSites)
    (hfreezeB' : ∀ t, Set.EqOn (B' t) (raw false) (inner false).insideSites)
    (hreadA : SourceOneTimeReading quadsA pocket inner (fun a => if a then A' else A))
    (hreadB : SourceOneTimeReading quadsB pocket inner (fun a => if a then B else B')) :
    TransmittedAnnotations D x z A B A' B'
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  apply transmittedAnnotations_of_plane_necklace_dependence quadsA quadsB outerA outerB
    D x z A B A' B' (inner false) (inner true) (raw false) (raw true)
  · apply source_reading_pair_square_dependence quadsA pocket D x z hx hz hD inner
      (fun a => if a then A' else A) raw
    · intro a t
      cases a
      · exact hfreezeA t
      · exact hfreezeA' t
    · exact hreadA
  · apply source_reading_pair_square_dependence quadsB pocket D x z hx hz hD inner
      (fun a => if a then B else B') raw
    · intro a t
      cases a
      · exact hfreezeB' t
      · exact hfreezeB t
    · exact hreadB

/-- Actual failed-seam probability at the permitted microscopic/fixed-square
normalization. It contains no signed kernel or pair dynamics. -/
def SourceFixedSquareFailure {Λ : Finset Site} {n : ℕ}
    (layouts : Fin n → SourceSeamLayout) (mic sq : Probe) (a b ε : ℝ) : Prop :=
  probability (sourceLaw Λ) (fun ω =>
    AdaptiveExchange.select (fun i => (layouts i).success) (List.finRange n) ω=none ∧
    SourceE mic sq (complete ω.1) (complete ω.2)) ≤ ε*(a*b)

/-- Finite specialization of the source failure conclusion, with source
symmetry proved for the literal plane-necklace event. -/
theorem source_fixed_square_failure_both_orientations {Λ : Finset Site} {n : ℕ}
    (layouts : Fin n → SourceSeamLayout) (mic sq : Probe) (a b ε : ℝ)
    (h : SourceFixedSquareFailure (Λ := Λ) layouts mic sq a b ε) :
    2*(probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select (fun i => (layouts i).success) (List.finRange n) ω=none ∧
      SourceE mic sq (complete ω.1) (complete ω.2)) +
    probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select (fun i => (layouts i).success) (List.finRange n) ω=none ∧
      SourceE mic sq (complete ω.2) (complete ω.1))) ≤ 4*ε*(a*b) := by
  rw [source_failure_symmetry (fun i => (layouts i).success) (List.finRange n)
    (fun i => (layouts i).success_swap) mic sq]
  change _ ≤ ε*(a*b) at h
  linarith

/-- The selected source layouts automatically satisfy the exact adaptive
invariance required by the pair response proof. This is a refinement theorem
for the literal PlaneNecklaceSuccess predicate, not an extra source premise. -/
theorem source_layouts_invariant {Λ : Finset Site} {n : ℕ}
    (layouts : Fin n → SourceSeamLayout)
    (hnested : ∀ i j, j=i ∨ (layouts j).support ⊆ (layouts i).inside ∨
      Disjoint (layouts j).support (layouts i).inside) :
    ∀ i (ω : Sources Λ), (layouts i).success ω=true → ∀ j,
      (layouts j).success (seamSwap (layouts i).inside ω)=(layouts j).success ω := by
  exact trial_invariance_of_nested_supports
    (fun i => (layouts i).success (Λ := Λ)) (fun i => (layouts i).inside)
    (fun i => (layouts i).support) (fun i => (layouts i).success_supported)
    (fun i => (layouts i).success_swap) (fun i => (layouts i).success_inside_swap) hnested

/-- Direct quantitative composition with the finite signed-response
theorem. This conclusion is NEW pair/square algebra; it is not named as
part of the published source input. -/
theorem source_failure_signed_error {Λ : Finset Site} {n : ℕ}
    (layouts : Fin n → SourceSeamLayout) (mic sq : Probe) (a b ε : ℝ)
    (L R : Sources Λ → ℝ)
    (hnested : ∀ i j, j=i ∨ (layouts j).support ⊆ (layouts i).inside ∨
      Disjoint (layouts j).support (layouts i).inside)
    (hL : ∀ ω, |L ω| ≤ 2) (hR : ∀ ω, |R ω| ≤ 2)
    (hsL : ∀ ω, L ω ≠ 0 → SourceE mic sq (complete ω.1) (complete ω.2))
    (hsR : ∀ ω, R ω ≠ 0 → SourceE mic sq (complete ω.2) (complete ω.1))
    (hgood : ∀ ω,
      AdaptiveExchange.select (fun i => (layouts i).success) (List.finRange n) ω ≠ none →
      L ω=R (AdaptiveExchange.applyFirst (fun i => (layouts i).success)
        (fun i => seamSwap (layouts i).inside) (List.finRange n) ω))
    (hfailure : SourceFixedSquareFailure (Λ := Λ) layouts mic sq a b ε) :
    |(sourceLaw Λ).expect L-(sourceLaw Λ).expect R| ≤ 4*ε*(a*b) := by
  exact (adaptive_failure_weighting (fun i => (layouts i).success)
    (fun i => (layouts i).inside) (List.finRange n) (source_layouts_invariant layouts hnested)
    mic sq L R 2 hL hR hsL hsR hgood).trans
      (source_fixed_square_failure_both_orientations layouts mic sq a b ε hfailure)

#print axioms source_reading_pair_square_dependence
#print axioms source_one_time_reading_of_relation
#print axioms source_readings_transmitted
#print axioms source_fixed_square_failure_both_orientations
#print axioms source_layouts_invariant
#print axioms source_failure_signed_error


/-- A finite, checkable placement certificate. The outer sleeve lies in a
centered axial box. Each tested quad either contains that box away from
its terminals or has its entire domain disjoint from it. -/
def SourceSeamLayout.QuadPlacement {Q : Type*} (J : SourceSeamLayout)
    (quads : Q → GraphQuad) : Prop :=
  ∃ c : Site, ∃ n : ℕ,
    (∀ v ∈ J.outerSleeve, v-c ∈ latticeBox n) ∧
    ∀ q, (∀ v ∈ (quads q).domain, v-c ∉ latticeBox n) ∨
      ((∀ v, v-c ∈ latticeBox n → v ∈ (quads q).domain) ∧
      (∀ v ∈ (quads q).firstSide, v-c ∉ latticeBox n) ∧
      (∀ v ∈ (quads q).secondSide, v-c ∉ latticeBox n))

theorem SourceSeamLayout.QuadPlacement.outer {Q : Type*} {J : SourceSeamLayout}
    {quads : Q → GraphQuad} (h : J.QuadPlacement quads) (C : NecklaceShape)
    (hC : C.vertices ⊆ J.outerSleeve) :
    ∀ q, (∀ v ∈ (quads q).domain, v ∉ C.insideSites) ∨
      (C.insideSites ⊆ ((quads q).domain : Set Site) ∧
      ((quads q).firstSide : Set Site) ⊆ C.outsideSites ∧
      ((quads q).secondSide : Set Site) ⊆ C.outsideSites) := by
  obtain ⟨c,n,hs,hQ⟩ := h
  have hin := C.insideSites_centered_box c n (fun v hv => hs v (hC hv))
  intro q
  rcases hQ q with hd | ⟨hq,hfirst,hsecond⟩
  · exact Or.inl (fun v hv hi => hd v hv (hin v hi))
  · refine Or.inr ⟨?_,?_,?_⟩
    · intro v hv
      exact hq v (hin v hv)
    · intro v hv
      exact Or.inl (fun hi => hfirst v hv (hin v hi))
    · intro v hv
      exact Or.inl (fun hi => hsecond v hv (hin v hi))

/-- The source-derived existence/failure boundary, retaining the order
"finite positive trial radii, then fixed square, then mesh". `a` and `b`
must be matched to the source costs A_e(b_e,1) and A_e(h,1), and the probes
must be matched through the proved buffered circular/graph-cut dictionary
before this predicate is supplied from source06 (many-trials, lines730-757).

This is an explicit theorem parameter, not a global axiom. In particular,
the definition does not assert this statement for arbitrary cost functions
or probe families. It deliberately contains no pair kernel, signed response,
or dynamical probability. Actual insertion and quad placement are explicit;
one-time reading is derived below. -/
def OpenAI2026FixedSquareSeams {Mesh Square Location QA QB : Type*}
    (meshFilter : Filter Mesh) (squareFilter : Filter Square)
    (quadsA : Square → Mesh → Location → QA → GraphQuad)
    (quadsB : Square → Mesh → Location → QB → GraphQuad) (z : Site) (trialCap : ℝ)
    (squareSites : Square → Mesh → Location → Finset Site)
    (sites : Square → Mesh → Location → Finset Site)
    (mic sq : Square → Mesh → Location → Probe)
    (a : Mesh → ℝ) (b : Square → Mesh → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∃ radii : Fin n → ℝ,
    ∃ enlargement : ℝ, 1 ≤ enlargement ∧
    (∀ i, 0 < radii i ∧ enlargement*radii i < trialCap) ∧
    ∀ᶠ h in squareFilter, ∀ᶠ e in meshFilter, ∀ x,
      ∃ layouts : Fin n → SourceSeamLayout,
        (∀ i, (layouts i).Circular (sites h e x) (mic h e x).mesh
          (mic h e x).center (radii i)) ∧
        (∀ i v, v ∈ (layouts i).support →
          radii i / enlargement ≤ dist (position (mic h e x).mesh v)
            (position (mic h e x).mesh (mic h e x).center) ∧
          dist (position (mic h e x).mesh v)
            (position (mic h e x).mesh (mic h e x).center) ≤ enlargement*radii i) ∧
        (∀ i j, j=i ∨ (layouts j).support ⊆ (layouts i).inside ∨
          Disjoint (layouts j).support (layouts i).inside) ∧
        (∀ i, (mic h e x).center ∈ (layouts i).pocket ∧
          (mic h e x).center+z ∈ (layouts i).pocket ∧
          squareSites h e x ⊆ (layouts i).pocket ∧
          (layouts i).QuadPlacement (quadsA h e x) ∧
          (layouts i).QuadPlacement (quadsB h e x)) ∧
        SourceFixedSquareFailure (Λ := sites h e x) layouts
          (mic h e x) (sq h e x) (a e) (b h e) ε

/-- Literal sewn fair fields have the fixed source interior and exterior
required by the one-time necklace reading. This is a deterministic dictionary,
not an assumption about the dynamics or the response kernel. -/
theorem source_sewn_reading (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {Q : Type*} (J : SourceSeamLayout) (quads : Q → GraphQuad)
    (ω : Sources Λ) (exterior : Bool) (inner : Bool → NecklaceShape)
    (outer : NecklaceShape)
    (hrel : ∀ a, J.relation (inner a) outer (sewnField J.inside ω a exterior))
    (hplace : J.QuadPlacement quads) :
    SourceOneTimeReading quads J.pocket inner
      (fun a _ => complete (sewnField J.inside ω a exterior)) := by
  have hout := hplace.outer outer (hrel false).1.2.1
  have hninside : ∀ v ∈ outer.outsideSites, v ∉ J.inside := by
    intro v hv hin
    rcases hv with hv | hv
    · exact hv ((hrel false).2.2.1 hin)
    · exact Finset.disjoint_left.mp (hrel false).2.2.2 hv hin
  have hext : ∀ a b, Set.EqOn (complete (sewnField J.inside ω a exterior))
      (complete (sewnField J.inside ω b exterior)) outer.outsideSites := by
    intro a b v hv
    have hvIn := hninside v hv
    by_cases hvΛ : v ∈ Λ <;> simp [complete,sewnField,hvΛ,hvIn]
  intro q t a b ξ η hξ hη hbit
  rcases hout q with hd | hc
  · apply (quads q).test_congr
    intro v hv
    have hvout : v ∈ outer.outsideSites := Or.inl (hd v hv)
    have hvp : v ∉ J.pocket := fun hp => hninside v hvout (J.pocket_inside hp)
    exact (hξ hvp).trans ((hext a b hvout).trans (hη hvp).symm)
  · have hr := source_one_time_reading_of_relation hexInput J (fun _ : Unit => quads q)
      ω exterior inner outer (fun a _ => complete (sewnField J.inside ω a exterior)) hrel
      (fun _ _ _ _ => rfl) (fun a b _ => hext a b)
      (fun _ => hc.1) (fun _ => hc.2.1) (fun _ => hc.2.2)
    exact hr () t a b ξ η hξ hη hbit

theorem source_sewn_frozen {Λ : Finset Site} (J : SourceSeamLayout)
    (ω : Sources Λ) (a b : Bool) (C : NecklaceShape)
    (hin : C.insideSites ⊆ (J.inside : Set Site)) :
    Set.EqOn (complete (sewnField J.inside ω a b))
      (complete (if a then ω.2 else ω.1)) C.insideSites := by
  intro v hv
  have hvIn : v ∈ J.inside := hin hv
  cases a <;> by_cases hvΛ : v ∈ Λ <;> simp [complete,sewnField,hvΛ,hvIn]

/-- The actual successful four-way event supplies all four transmitted
pair/square evaluations for the two raw fair source fields and their literal
interior exchange. No signed identity or transmission is assumed. -/
theorem source_success_transmitted_raw (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {QA QB : Type*} (J : SourceSeamLayout)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (D : Finset Site) (x z : Site) (ω : Sources Λ)
    (hx : x ∈ J.pocket) (hz : x+z ∈ J.pocket) (hD : D ⊆ J.pocket)
    (hplaceA : J.QuadPlacement quadsA) (hplaceB : J.QuadPlacement quadsB)
    (hsuccess : J.success ω=true) :
    TransmittedAnnotations D x z
      (fun _ => complete ω.1) (fun _ => complete ω.2)
      (fun _ => complete (seamSwap J.inside ω).1)
      (fun _ => complete (seamSwap J.inside ω).2)
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  have hsuccess' : FourWaySuccess J.inside J.relation ω := of_decide_eq_true hsuccess
  obtain ⟨inner,outer,hrel⟩ := hsuccess'
  have hreadA := source_sewn_reading hexInput J quadsA ω false inner (outer false)
    (fun a => hrel a false) hplaceA
  have hreadB := source_sewn_reading hexInput J quadsB ω true inner (outer true)
    (fun a => hrel a true) hplaceB
  have hfreeze (a b t : Bool) := source_sewn_frozen J ω a b (inner a) (hrel a b).2.1
  have hs0 : sewnField J.inside ω false false=ω.1 := by
    funext v
    simp [sewnField]
  have hs1 : sewnField J.inside ω true true=ω.2 := by
    funext v
    simp [sewnField]
  have hs10 : sewnField J.inside ω true false=(seamSwap J.inside ω).1 := rfl
  have hs01 : sewnField J.inside ω false true=(seamSwap J.inside ω).2 := rfl
  apply source_readings_transmitted quadsA quadsB outerA outerB J.pocket D x z hx hz hD
    inner (fun a => complete (if a then ω.2 else ω.1))
  · simpa only [hs0] using hfreeze false false
  · simpa only [hs1] using hfreeze true true
  · simpa only [hs10] using hfreeze true false
  · simpa only [hs01] using hfreeze false true
  · convert hreadA using 1
    funext a t
    cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,hs0,hs10]
  · convert hreadB using 1
    funext a t
    cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true,hs1,hs01]

/-- New pair/square conclusion of the source's literal successful seam.
Both supported pair rules use their already proved monotone-table response. -/
theorem source_success_raw_signed_exchange (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {QA QB : Type*} (J : SourceSeamLayout)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (D : Finset Site) (x z : Site) (rule : Rule) (ω : Sources Λ)
    (hx : x ∈ J.pocket) (hz : x+z ∈ J.pocket) (hD : D ⊆ J.pocket)
    (hplaceA : J.QuadPlacement quadsA) (hplaceB : J.QuadPlacement quadsB)
    (hsuccess : J.success ω=true) :
    rawPairResponse rule.kernel (fun _ => complete ω.1) x z
        (fun ξ => outerA (crossingVector quadsA ξ)) *
      rawSquareResponse D (fun _ => complete ω.2) (fun ξ => outerB (crossingVector quadsB ξ)) =
    rawSquareResponse D (fun _ => complete (seamSwap J.inside ω).1)
        (fun ξ => outerA (crossingVector quadsA ξ)) *
      rawPairResponse rule.kernel (fun _ => complete (seamSwap J.inside ω).2) x z
        (fun ξ => outerB (crossingVector quadsB ξ)) := by
  obtain ⟨φ,ψ,f,g,hφ,hψ,hAF,hBG,hA'F,hB'G⟩ := source_success_transmitted_raw hexInput J
    quadsA quadsB outerA outerB D x z ω hx hz hD hplaceA hplaceB hsuccess
  exact successful_signed_exchange rule.kernel D x z _ _ _ _ _ _ φ ψ f g
    (rule.amplitude φ) (rule.response φ hφ) hψ hAF hBG hA'F hB'G

#print axioms source_success_transmitted_raw
#print axioms source_success_raw_signed_exchange


/-- Single-insertion pair/square comparison obtained from the source's
actual failed-seam event. The local-change arm implications are deterministic
quad/probe statements; all raw source probabilities and successful-seam
response identities are the ones already defined above. -/
theorem source_raw_pair_square_bound (hexInput : PublishedPlaneDiskHex)
    {Λ : Finset Site} {n : ℕ} {QA QB : Type*}
    (layouts : Fin n → SourceSeamLayout) (mic sq : Probe) (z : Site)
    (D : Finset Site) (rule : Rule)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (a b ε : ℝ)
    (hnested : ∀ i j, j=i ∨ (layouts j).support ⊆ (layouts i).inside ∨
      Disjoint (layouts j).support (layouts i).inside)
    (hboundA : ∀ c, |outerA c| ≤ 1) (hboundB : ∀ c, |outerB c| ≤ 1)
    (hlocalAmic : ∀ q, LocalChangeArms (quadsA q) mic)
    (hlocalAsq : ∀ q, LocalChangeArms (quadsA q) sq)
    (hlocalBmic : ∀ q, LocalChangeArms (quadsB q) mic)
    (hlocalBsq : ∀ q, LocalChangeArms (quadsB q) sq)
    (hpair : mic.center ∈ mic.pocket ∧ mic.center+z ∈ mic.pocket)
    (hD : (D : Set Site) ⊆ sq.pocket)
    (hxtrial : ∀ i, mic.center ∈ (layouts i).pocket)
    (hztrial : ∀ i, mic.center+z ∈ (layouts i).pocket)
    (hDtrial : ∀ i, D ⊆ (layouts i).pocket)
    (hplaceA : ∀ i, (layouts i).QuadPlacement quadsA)
    (hplaceB : ∀ i, (layouts i).QuadPlacement quadsB)
    (hfailure : SourceFixedSquareFailure (Λ := Λ) layouts mic sq a b ε) :
    |(sourceLaw Λ).expect (fun ω =>
        rawPairResponse rule.kernel (fun _ => complete ω.1) mic.center z
          (fun ξ => outerA (crossingVector quadsA ξ)) *
        rawSquareResponse D (fun _ => complete ω.2)
          (fun ξ => outerB (crossingVector quadsB ξ))) -
      (sourceLaw Λ).expect (fun ω =>
        rawSquareResponse D (fun _ => complete ω.1)
          (fun ξ => outerA (crossingVector quadsA ξ)) *
        rawPairResponse rule.kernel (fun _ => complete ω.2) mic.center z
          (fun ξ => outerB (crossingVector quadsB ξ)))| ≤ 4*ε*(a*b) := by
  apply (pair_square_sewing_failure_bound
    (fun i => (layouts i).success (Λ := Λ)) (fun i => (layouts i).inside) (List.finRange n)
    (source_layouts_invariant layouts hnested) mic sq z D rule
    (fun ω _ => complete ω.1) (fun ω _ => complete ω.2)
    quadsA quadsB outerA outerB hboundA hboundB
    hlocalAmic hlocalAsq hlocalBmic hlocalBsq hpair hD
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ?_).trans
    (source_fixed_square_failure_both_orientations layouts mic sq a b ε hfailure)
  intro ω hs
  cases hselect : AdaptiveExchange.select (fun i => (layouts i).success) (List.finRange n) ω with
  | none => exact False.elim (hs hselect)
  | some i =>
    simpa only [AdaptiveExchange.applyFirst,hselect] using
      source_success_transmitted_raw hexInput (layouts i) quadsA quadsB outerA outerB
        D mic.center z ω (hxtrial i) (hztrial i) (hDtrial i) (hplaceA i) (hplaceB i)
        (AdaptiveExchange.selected_success _ _ ω i hselect)

#print axioms source_raw_pair_square_bound


/-- Exact factorization of the two original independent fair fields. -/
theorem source_expect_product {Λ : Finset Site} (f g : (↥Λ → Bool) → ℝ) :
    (sourceLaw Λ).expect (fun ω => f ω.1*g ω.2) =
      (ProbeProduct.fairSites ↥Λ).expect f * (ProbeProduct.fairSites ↥Λ).expect g := by
  rw [sourceLaw,FiniteLaw.expect_prod]
  simp_rw [FiniteLaw.expect_const_mul]
  exact FiniteLaw.expect_mul_const _ _ _

noncomputable def averagedPairResponse (Λ : Finset Site) (rule : Rule) (x z : Site)
    (F : TwoTimeConfiguration → ℝ) : ℝ :=
  (ProbeProduct.fairSites ↥Λ).expect (fun ω =>
    rawPairResponse rule.kernel (fun _ => complete ω) x z F)

noncomputable def averagedSquareResponse (Λ : Finset Site) (D : Finset Site)
    (F : TwoTimeConfiguration → ℝ) : ℝ :=
  (ProbeProduct.fairSites ↥Λ).expect (fun ω =>
    rawSquareResponse D (fun _ => complete ω) F)

/-- Identification with the actual common-square algebra, before any limit.
The calibrating square response is the same for both pair rules. -/
theorem source_raw_error_eq_squareError (Λ : Finset Site) (rule : Rule)
    (D : Finset Site) (x z : Site) (F G : TwoTimeConfiguration → ℝ) :
    (sourceLaw Λ).expect (fun ω =>
        rawPairResponse rule.kernel (fun _ => complete ω.1) x z F *
        rawSquareResponse D (fun _ => complete ω.2) G) -
      (sourceLaw Λ).expect (fun ω =>
        rawSquareResponse D (fun _ => complete ω.1) F *
        rawPairResponse rule.kernel (fun _ => complete ω.2) x z G) =
      CommonSquare.squareError (averagedPairResponse Λ rule x z F)
        (averagedPairResponse Λ rule x z G) (averagedSquareResponse Λ D F)
        (averagedSquareResponse Λ D G) := by
  rw [source_expect_product (fun ω => rawPairResponse rule.kernel (fun _ => complete ω) x z F)
    (fun ω => rawSquareResponse D (fun _ => complete ω) G),
    source_expect_product (fun ω => rawSquareResponse D (fun _ => complete ω) F)
    (fun ω => rawPairResponse rule.kernel (fun _ => complete ω) x z G)]
  rfl

#print axioms source_raw_error_eq_squareError
end ExceptionalTimes.PairSquareSewing





