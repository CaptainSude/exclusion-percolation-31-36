import ExceptionalTimes.SourceTrialSymmetry
import ExceptionalTimes.FiniteSiteLaw

open Set
open scoped Classical BigOperators

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance FiniteHaar

/-- A literal monochromatic crossing with the same finite domain and
terminal sets as GraphQuad.Crossing. -/
def GraphQuad.ColorCrossing (Q : GraphQuad) (color : Bool) (ω : Configuration) : Prop :=
  ∃ u ∈ Q.firstSide, ∃ v ∈ Q.secondSide, ∃ p : triangularGraph.Walk u v,
    ∀ z ∈ p.support, z ∈ Q.domain ∧ ω z = color

/-- An actual connector requirement in one of the four sewn fields.
An arbitrary finite family allows rectangle chains and repeated use of
source bits; no independence of the sewn configurations is asserted. -/
structure SewnConnector where
  quad : GraphQuad
  color : Bool
  innerSource : Bool
  outerSource : Bool

def SewnConnector.event {Λ : Finset Site} (C : SewnConnector) (inside : Finset Site)
    (ω : Sources Λ) : Prop :=
  C.quad.ColorCrossing C.color (complete (sewnField inside ω C.innerSource C.outerSource))

def polarizeField {Λ : Finset Site} (white : Finset Site) (ω : ↥Λ → Bool) : ↥Λ → Bool :=
  fun v => if (v:Site) ∈ white then !(ω v) else ω v

def polarizeSources {Λ : Finset Site} (white : Finset Site) (ω : Sources Λ) : Sources Λ :=
  (polarizeField white ω.1,polarizeField white ω.2)

theorem polarizeSources_involutive {Λ : Finset Site} (white : Finset Site) :
    Function.Involutive (polarizeSources (Λ := Λ) white) := by
  intro ω
  apply Prod.ext <;> funext v <;> by_cases hv : (v:Site) ∈ white <;>
    simp [polarizeSources,polarizeField,hv]

theorem sewnField_polarize {Λ : Finset Site} (inside white : Finset Site) (ω : Sources Λ)
    (a b : Bool) (v : ↥Λ) :
    sewnField inside (polarizeSources white ω) a b v =
      if (v:Site) ∈ white then !(sewnField inside ω a b v) else sewnField inside ω a b v := by
  by_cases hi : (v:Site) ∈ inside <;> by_cases hw : (v:Site) ∈ white <;>
    cases a <;> cases b <;> simp [sewnField,polarizeSources,polarizeField,hi,hw]

theorem sewnField_mono {Λ : Finset Site} (inside : Finset Site) (a b : Bool)
    {ω η : Sources Λ} (h : ω ≤ η) : sewnField inside ω a b ≤ sewnField inside η a b := by
  intro v
  by_cases hi : (v:Site) ∈ inside <;> cases a <;> cases b <;>
    simp only [sewnField,hi,ite_true,ite_false,Bool.false_eq_true] <;>
    first | exact h.1 v | exact h.2 v

/-- Every connector domain uses its own color's sites. This is exactly
the coordinate separation required for the source's favorable product
order, stated on original site coordinates. -/
def SewnConnector.Fits (C : SewnConnector) (Λ white : Finset Site) : Prop :=
  C.quad.domain ⊆ Λ ∧ ∀ v ∈ C.quad.domain, (v ∈ white ↔ C.color = false)

theorem SewnConnector.fits_of_separated (C : SewnConnector) (Λ black white : Finset Site)
    (hdis : Disjoint black white) (hB : black ⊆ Λ) (hW : white ⊆ Λ)
    (hdom : C.quad.domain ⊆ if C.color then black else white) : C.Fits Λ white := by
  cases hc : C.color
  · simp only [hc,Bool.false_eq_true,ite_false] at hdom
    exact ⟨hdom.trans hW,fun v hv => ⟨fun _ => hc,fun _ => hdom hv⟩⟩
  · simp only [hc,ite_true] at hdom
    refine ⟨hdom.trans hB,?_⟩
    intro v hv
    simp only [hc,Bool.true_eq_false,iff_false]
    exact fun hw => Finset.disjoint_left.mp hdis (hdom hv) hw

theorem SewnConnector.event_polarized_mono {Λ : Finset Site} (C : SewnConnector)
    (inside white : Finset Site) (hfit : C.Fits Λ white)
    {ω η : Sources Λ} (h : ω ≤ η) :
    C.event inside (polarizeSources white ω) → C.event inside (polarizeSources white η) := by
  rintro ⟨u,hu,v,hv,p,hp⟩
  refine ⟨u,hu,v,hv,p,?_⟩
  intro z hz
  obtain ⟨hzdom,hzcolor⟩ := hp z hz
  refine ⟨hzdom,?_⟩
  have hzΛ := hfit.1 hzdom
  have hbit := sewnField_mono inside C.innerSource C.outerSource h ⟨z,hzΛ⟩
  change complete (sewnField inside (polarizeSources white ω) C.innerSource C.outerSource) z = C.color at hzcolor
  change complete (sewnField inside (polarizeSources white η) C.innerSource C.outerSource) z = C.color
  simp only [complete,hzΛ,dite_eq_left,sewnField_polarize] at hzcolor ⊢
  have hwhite := hfit.2 z hzdom
  cases hc : C.color
  · have hw : z ∈ white := hwhite.mpr hc
    simp only [hw,ite_true,hc,Bool.not_eq_false_eq_eq_true] at hzcolor ⊢
    rw [hzcolor] at hbit
    exact top_le_iff.mp hbit
  · have hw : z ∉ white := fun hw => by simpa [hc] using hwhite.mp hw
    simp only [hw,ite_false,hc] at hzcolor ⊢
    rw [hzcolor] at hbit
    exact top_le_iff.mp hbit

theorem sourceLaw_expect_eq_average {Λ : Finset Site} (f : Sources Λ → ℝ) :
    (sourceLaw Λ).expect f = average f := by
  rw [sourceLaw,FiniteLaw.expect_prod,FiniteSiteLaw.fairSites_expect_eq_average]
  simp only [FiniteSiteLaw.fairSites_expect_eq_average]
  exact (FiniteSiteLaw.average_prod f).symm

theorem sourceLaw_polarize_probability {Λ : Finset Site} (white : Finset Site)
    (E : Sources Λ → Prop) :
    probability (sourceLaw Λ) (fun ω => E (polarizeSources white ω)) = probability (sourceLaw Λ) E := by
  let e : Sources Λ ≃ Sources Λ := (polarizeSources_involutive white).toPerm
  simp only [probability,sourceLaw_expect_eq_average]
  exact average_equiv e (fun ω => indicator (E ω))

theorem uniform_harris_finite_product {X I : Type*} [Fintype X] [Nonempty X]
    [DistribLattice X] [DecidableEq I] (s : Finset I) (f : I → X → ℝ)
    (hf : ∀ i ∈ s, Monotone (f i)) (hf0 : ∀ i ∈ s, ∀ x, 0 ≤ f i x) :
    (∏ i ∈ s, average (f i)) ≤ average (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simp [average_const]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hs : ∏ j ∈ s, average (f j) ≤ average (fun x => ∏ j ∈ s, f j x) :=
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hf0 j (Finset.mem_insert_of_mem hj))
    have hi0 : 0 ≤ average (f i) := average_nonneg (hf0 i (Finset.mem_insert_self ..))
    have hmul := mul_le_mul_of_nonneg_left hs hi0
    have hH := uniform_harris (f i) (fun x => ∏ j ∈ s, f j x)
      (hf0 i (Finset.mem_insert_self ..))
      (fun x => Finset.prod_nonneg (fun j hj => hf0 j (Finset.mem_insert_of_mem hj) x))
      (hf i (Finset.mem_insert_self ..)) (by
        intro x y hxy
        exact Finset.prod_le_prod₀ (fun j hj => hf0 j (Finset.mem_insert_of_mem hj) x)
          (fun j hj => hf j (Finset.mem_insert_of_mem hj) hxy))
    simpa only [Finset.prod_insert hi] using hmul.trans hH

/-- Positive association for all literal connector crossings, including
the four sewn combinations with their shared source bits. Lower bounds
multiply by Harris under one favorable order, not by independence. -/
theorem sewn_connector_joint_bound {Λ : Finset Site} {I : Type*} [Fintype I]
    (connectors : I → SewnConnector) (inside white : Finset Site)
    (hfit : ∀ i, (connectors i).Fits Λ white) :
    (∏ i, probability (sourceLaw Λ) ((connectors i).event inside)) ≤
      probability (sourceLaw Λ) (fun ω => ∀ i, (connectors i).event inside ω) := by
  classical
  let f (i : I) (ω : Sources Λ) := indicator ((connectors i).event inside (polarizeSources white ω))
  have hf (i : I) : Monotone (f i) := by
    intro ω η hωη
    by_cases hω : (connectors i).event inside (polarizeSources white ω)
    · have hη := (connectors i).event_polarized_mono inside white (hfit i) hωη hω
      simp [f,EnvironmentVariance.indicator,hω,hη]
    · simpa only [f,EnvironmentVariance.indicator,hω,ite_false] using indicator_nonneg
        ((connectors i).event inside (polarizeSources white η))
  have h := uniform_harris_finite_product Finset.univ f (fun i _ => hf i)
    (fun i _ ω => indicator_nonneg _)
  have hprob (i : I) : average (f i) = probability (sourceLaw Λ) ((connectors i).event inside) := by
    rw [←sourceLaw_polarize_probability white]
    simp only [probability,sourceLaw_expect_eq_average,f]
  have hprod : average (fun ω => ∏ i, f i ω) =
      probability (sourceLaw Λ) (fun ω => ∀ i, (connectors i).event inside ω) := by
    rw [←sourceLaw_polarize_probability white]
    simp only [probability,sourceLaw_expect_eq_average,f,ProbeProduct.indicator_forall]
  simpa only [hprob,hprod] using h

#print axioms SewnConnector.event_polarized_mono
#print axioms sewn_connector_joint_bound

end ExceptionalTimes.PairSquareSewing
