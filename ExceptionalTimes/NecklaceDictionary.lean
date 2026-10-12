import ExceptionalTimes.PairSquareTrials

/-!
Deterministic dictionary between actual graph joins and two-time signed
annotations. The geometric content of the necklace lemma is isolated as
one-time crossing dependence on the join. The monotone truth tables,
coordinatewise time action, and common exterior tests are derived here.
This module does not prove the polygon/cell or necklace construction.
-/

open scoped BigOperators Classical

namespace ExceptionalTimes.PairSquareSewing

open DimerBinaryResponse

theorem GraphQuad.crossing_congr (Q : GraphQuad) {ω η : Configuration}
    (h : Set.EqOn ω η (Q.domain : Set Site)) : Q.Crossing ω ↔ Q.Crossing η := by
  constructor
  · rintro ⟨u, hu, v, hv, p, hp⟩
    refine ⟨u, hu, v, hv, p, fun z hz => ⟨(hp z hz).1, ?_⟩⟩
    rw [← h (hp z hz).1]
    exact (hp z hz).2
  · rintro ⟨u, hu, v, hv, p, hp⟩
    refine ⟨u, hu, v, hv, p, fun z hz => ⟨(hp z hz).1, ?_⟩⟩
    rw [h (hp z hz).1]
    exact (hp z hz).2

theorem GraphQuad.test_congr (Q : GraphQuad) {ω η : Configuration}
    (h : Set.EqOn ω η (Q.domain : Set Site)) : Q.test ω = Q.test η := by
  simp only [GraphQuad.test, Q.crossing_congr h]

theorem GraphQuad.test_mono (Q : GraphQuad) {ω η : Configuration}
    (h : ∀ v, ω v = true → η v = true) : Q.test ω = true → Q.test η = true := by
  simp only [GraphQuad.test, decide_eq_true_eq]
  exact Q.crossing_mono h

/-- Tested quads disjoint from the local pocket need no bulk arm
argument: their crossing cannot change under the local overwrite. -/
theorem localChangeArms_of_domain_disjoint (Q : GraphQuad) (P : Probe)
    (hdisjoint : Disjoint (Q.domain : Set Site) P.pocket) : LocalChangeArms Q P := by
  intro ω a b hout _ _ hchange
  apply False.elim
  apply hchange
  apply Q.test_congr
  intro v hv
  apply hout v
  exact fun hp => Set.disjoint_left.mp hdisjoint hv hp

theorem putPair_mono (ω : Configuration) (x z : Site) {u v u' v' : Bool}
    (hu : u = true → u' = true) (hv : v = true → v' = true) :
    ∀ y, putPair ω x z u v y = true → putPair ω x z u' v' y = true := by
  intro y hy
  by_cases hz : y = x + z
  · simpa [putPair, hz] using hv (by simpa [putPair, hz] using hy)
  · by_cases hx : y = x
    · subst y
      simpa [putPair, hz] using hu (by simpa [putPair, hz] using hy)
    · simpa [putPair, hz, hx] using hy

/-- Q is the actual join domain with its two black runs as terminals. -/
noncomputable def pairJoinTable (Q : GraphQuad) (ω : Configuration) (x z : Site) : Table :=
  Table.ofFunction (fun u v => Q.test (putPair ω x z u v))

@[simp] theorem pairJoinTable_eval (Q : GraphQuad) (ω : Configuration)
    (x z : Site) (u v : Bool) :
    (pairJoinTable Q ω x z).eval u v = Q.test (putPair ω x z u v) :=
  Table.eval_ofFunction _ u v

/-- This is graph-path monotonicity, not an additional necklace hypothesis. -/
theorem pairJoinTable_increasing (Q : GraphQuad) (ω : Configuration) (x z : Site) :
    Increasing (pairJoinTable Q ω x z) := by
  change (Q.test (putPair ω x z false false) = true →
      Q.test (putPair ω x z false true) = true) ∧
    (Q.test (putPair ω x z false false) = true →
      Q.test (putPair ω x z true false) = true) ∧
    (Q.test (putPair ω x z false true) = true →
      Q.test (putPair ω x z true true) = true) ∧
    (Q.test (putPair ω x z true false) = true →
      Q.test (putPair ω x z true true) = true)
  exact ⟨Q.test_mono (putPair_mono ω x z id (by simp)),
    Q.test_mono (putPair_mono ω x z (by simp) id),
    Q.test_mono (putPair_mono ω x z (by simp) id),
    Q.test_mono (putPair_mono ω x z id (by simp))⟩

noncomputable def squareJoin (Q : GraphQuad) (ω : Configuration) (D : Finset Site) :
    Bool → Bool := fun b => Q.test (force D ω b)

theorem squareJoin_increasing (Q : GraphQuad) (ω : Configuration) (D : Finset Site) :
    squareJoin Q ω D false = true → squareJoin Q ω D true = true :=
  square_crossing_mono Q D ω

theorem putPair_congr_on (ω η : Configuration) (x z : Site) (u v : Bool)
    (S : Set Site) (h : Set.EqOn ω η S) :
    Set.EqOn (putPair ω x z u v) (putPair η x z u v) S := by
  intro y hy
  by_cases hz : y = x + z
  · simp [putPair, hz]
  · by_cases hx : y = x
    · subst y
      simp [putPair, hz]
    · simpa [putPair, hz, hx] using h hy

theorem force_congr_on (D : Finset Site) (ω η : Configuration) (b : Bool)
    (S : Set Site) (h : Set.EqOn ω η S) : Set.EqOn (force D ω b) (force D η b) S := by
  intro y hy
  by_cases hd : y ∈ D
  · simp [force, hd]
  · simpa [force, hd] using h hy

/-- All unannotated colors in the join domain are frozen across time.
Thus the same actual two-bit table acts at both observation times. -/
theorem pairHistory_join (Q : GraphQuad) (background : TwoTimeConfiguration)
    (ω : Configuration) (x z : Site)
    (hfrozen : ∀ t, Set.EqOn (background t) ω (Q.domain : Set Site))
    (a b : State) (t : Bool) :
    Q.test (pairHistory background x z a b t) =
      if t then (pairJoinTable Q ω x z).eval b.1 b.2
      else (pairJoinTable Q ω x z).eval a.1 a.2 := by
  cases t <;> simp only [pairHistory, Bool.false_eq_true, ↓reduceIte,
    pairJoinTable_eval]
  · exact Q.test_congr (putPair_congr_on _ _ x z _ _ _ (hfrozen false))
  · exact Q.test_congr (putPair_congr_on _ _ x z _ _ _ (hfrozen true))

theorem squareHistory_join (Q : GraphQuad) (D : Finset Site)
    (background : TwoTimeConfiguration) (ω : Configuration)
    (hfrozen : ∀ t, Set.EqOn (background t) ω (Q.domain : Set Site))
    (h : History) (t : Bool) :
    Q.test (squareHistory D background h t) =
      squareJoin Q ω D (if t then h.2 else h.1) := by
  exact Q.test_congr (force_congr_on D _ _ _ _ (hfrozen t))

/-- A pointwise event transfer, useful when checking a finite cylinder
against the source's full fair-field event. -/
theorem fourArms_congr (P : Probe) {ω η : Configuration}
    (h : Set.EqOn ω η P.region) : FourArms P ω ↔ FourArms P η := by
  have forward {a b : Configuration} (hab : Set.EqOn a b P.region)
      (ha : FourArms P a) : FourArms P b := by
    obtain ⟨start, finish, path, hp, hs, hf, hc, hd, contacts⟩ := ha
    refine ⟨start, finish, path, hp, hs, hf, ?_, hd, contacts⟩
    intro i z hz
    exact ⟨(hc i z hz).1, (hab (hc i z hz).1).symm.trans (hc i z hz).2⟩
  exact ⟨forward h, forward h.symm⟩

/-- Every color in the buffered arm request lies in its stated region;
completion outside a finite cylinder cannot alter this event. -/
theorem fourArms_complete_restrict (P : Probe) (Λ : Finset Site)
    (hΛ : P.region ⊆ (Λ : Set Site)) (ω : Configuration) :
    FourArms P (complete (fun v : ↥Λ => ω v)) ↔ FourArms P ω := by
  apply fourArms_congr
  intro v hv
  have hvΛ : v ∈ Λ := hΛ hv
  simp [complete, hvΛ]

theorem sourceE_complete_restrict (mic sq : Probe) (Λ : Finset Site)
    (hmic : mic.region ⊆ (Λ : Set Site)) (hsq : sq.region ⊆ (Λ : Set Site))
    (ω η : Configuration) :
    SourceE mic sq (complete (fun v : ↥Λ => ω v)) (complete (fun v : ↥Λ => η v)) ↔
      SourceE mic sq ω η := by
  exact and_congr (fourArms_complete_restrict mic Λ hmic ω)
    (fourArms_complete_restrict sq Λ hsq η)

/-- The join labels possible actual interiors, pairing a two-site
annotation with an imposed square annotation. -/
abbrev InteriorAnnotation := State ⊕ Bool

def annotationBit (φ : Table) (ψ : Bool → Bool) : InteriorAnnotation → Bool :=
  Sum.elim (fun a => φ.eval a.1 a.2) ψ

def annotationConfiguration (D : Finset Site) (x z : Site)
    (pairBackground squareBackground : TwoTimeConfiguration) (t : Bool) :
    InteriorAnnotation → Configuration :=
  Sum.elim (fun a => putPair (pairBackground t) x z a.1 a.2)
    (fun b => force D (squareBackground t) b)

/-- The one-time assertion supplied by the geometric necklace argument.
Both displayed interiors are read against the same exterior cut; other
inserted histories may be fixed arbitrarily outside that cut. This is an
event-level premise, with no signed response or error estimate in it. -/
def NecklaceCrossingDependence {Q : Type*} (quads : Q → GraphQuad)
    (D : Finset Site) (x z : Site) (pairBackground squareBackground : TwoTimeConfiguration)
    (φ : Table) (ψ : Bool → Bool) : Prop :=
  ∀ q t a b, annotationBit φ ψ a = annotationBit φ ψ b →
    (quads q).test (annotationConfiguration D x z pairBackground squareBackground t a) =
      (quads q).test (annotationConfiguration D x z pairBackground squareBackground t b)

/-- A reading function is constructed from dependence, rather than
postulated as a new two-time factorization assumption. -/
noncomputable def booleanReading {X : Type*} (bit test : X → Bool) (b : Bool) : Bool :=
  if h : ∃ a, bit a = b then test h.choose else false

theorem booleanReading_eq {X : Type*} (bit test : X → Bool)
    (h : ∀ a b, bit a = bit b → test a = test b) (a : X) :
    booleanReading bit test (bit a) = test a := by
  unfold booleanReading
  have ha : ∃ b, bit b = bit a := ⟨a, rfl⟩
  rw [dite_eq_left ha]
  exact h _ a ha.choose_spec

/-- Literal one-time crossing dependence implies the common two-time
exterior function for arbitrary functions of the tested crossings. -/
theorem crossing_dependence_transmissions {Q : Type*} (quads : Q → GraphQuad)
    (outer : (Q × Bool → Bool) → ℝ) (D : Finset Site) (x z : Site)
    (pairBackground squareBackground : TwoTimeConfiguration)
    (φ : Table) (ψ : Bool → Bool)
    (h : NecklaceCrossingDependence quads D x z pairBackground squareBackground φ ψ) :
    ∃ f : History → ℝ,
      PairTransmission pairBackground x z (fun ξ => outer (crossingVector quads ξ)) φ f ∧
      SquareTransmission D squareBackground (fun ξ => outer (crossingVector quads ξ)) ψ f := by
  let read := fun q t => booleanReading (annotationBit φ ψ)
    (fun a => (quads q).test (annotationConfiguration D x z pairBackground squareBackground t a))
  let f := fun history : History => outer (fun qt => read qt.1 qt.2
    (if qt.2 then history.2 else history.1))
  refine ⟨f, ?_, ?_⟩
  · intro a b
    apply congrArg outer
    funext qt
    cases ht : qt.2
    · simpa [crossingVector, pairHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 false) (.inl a)).symm
    · simpa [crossingVector, pairHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 true) (.inl b)).symm
  · intro history
    apply congrArg outer
    funext qt
    cases ht : qt.2
    · simpa [crossingVector, squareHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 false) (.inr history.1)).symm
    · simpa [crossingVector, squareHistory, ht, read, annotationConfiguration, annotationBit]
        using (booleanReading_eq _ _ (h qt.1 true) (.inr history.2)).symm

/-- The two source interiors provide actual graph join functions. Their
monotonicity and the four transported two-time evaluation equalities are
derived from the two one-time geometric dependence assertions. -/
theorem transmittedAnnotations_of_necklace_dependence
    {QA QB : Type*} (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (D : Finset Site) (x z : Site) (A B A' B' : TwoTimeConfiguration)
    (pairJoin squareJoinDomain : GraphQuad) (ω η : Configuration)
    (hA : NecklaceCrossingDependence quadsA D x z A A'
      (pairJoinTable pairJoin ω x z) (squareJoin squareJoinDomain η D))
    (hB : NecklaceCrossingDependence quadsB D x z B' B
      (pairJoinTable pairJoin ω x z) (squareJoin squareJoinDomain η D)) :
    TransmittedAnnotations D x z A B A' B'
      (fun ξ => outerA (crossingVector quadsA ξ))
      (fun ξ => outerB (crossingVector quadsB ξ)) := by
  obtain ⟨f, hAF, hA'F⟩ := crossing_dependence_transmissions quadsA outerA D x z A A' _ _ hA
  obtain ⟨g, hB'G, hBG⟩ := crossing_dependence_transmissions quadsB outerB D x z B' B _ _ hB
  exact ⟨pairJoinTable pairJoin ω x z, squareJoin squareJoinDomain η D, f, g,
    pairJoinTable_increasing pairJoin ω x z, squareJoin_increasing squareJoinDomain η D,
    hAF, hBG, hA'F, hB'G⟩

#print axioms pairJoinTable_increasing
#print axioms pairHistory_join
#print axioms fourArms_congr
#print axioms transmittedAnnotations_of_necklace_dependence

end ExceptionalTimes.PairSquareSewing

