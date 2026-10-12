import ExceptionalTimes.PairSquareTrials

/-!
The two orientations of the necessary source event have the same failed
trial probability, because success tests are source-symmetric and the
two raw fair fields have the identical law. This derives the factor four
in the signed sewing estimate from the actual finite source law.
-/

open scoped BigOperators Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance

/-- Equality of the two raw fields on an actual site support. -/
def SourceEqOn {Λ : Finset Site} (D : Finset Site) (ω η : Sources Λ) : Prop :=
  ∀ v : ↥Λ, (v : Site) ∈ D → ω.1 v = η.1 v ∧ ω.2 v = η.2 v

def SupportedSourceTest {Λ : Finset Site} (D : Finset Site) (f : Sources Λ → Bool) : Prop :=
  ∀ ω η, SourceEqOn D ω η → f ω = f η

theorem seamSwap_eqOn_inside {Λ : Finset Site} (D inside : Finset Site)
    (h : D ⊆ inside) (ω : Sources Λ) : SourceEqOn D (seamSwap inside ω) ω.swap := by
  intro v hv
  simp [seamSwap, h hv]

theorem seamSwap_eqOn_outside {Λ : Finset Site} (D inside : Finset Site)
    (h : Disjoint D inside) (ω : Sources Λ) : SourceEqOn D (seamSwap inside ω) ω := by
  intro v hv
  have hn : (v : Site) ∉ inside := fun hi => Finset.disjoint_left.mp h hv hi
  simp [seamSwap, hn]

/-- Disjoint nested annular supports give the cross-trial invariance:
smaller trials undergo a wholesale source swap, larger trials no change. -/
theorem trial_invariance_of_nested_supports {Λ : Finset Site} {I : Type*}
    (success : I → Sources Λ → Bool) (inside support : I → Finset Site)
    (hsupport : ∀ i, SupportedSourceTest (support i) (success i))
    (hsymmetric : ∀ i ω, success i ω.swap = success i ω)
    (hself : ∀ i ω, success i (seamSwap (inside i) ω) = success i ω)
    (hnested : ∀ i j, j = i ∨ support j ⊆ inside i ∨ Disjoint (support j) (inside i)) :
    ∀ i ω, success i ω = true →
      ∀ j, success j (seamSwap (inside i) ω) = success j ω := by
  intro i ω _ j
  rcases hnested i j with rfl | hin | hout
  · exact hself _ ω
  · exact (hsupport j _ _ (seamSwap_eqOn_inside _ _ hin ω)).trans (hsymmetric j ω)
  · exact hsupport j _ _ (seamSwap_eqOn_outside _ _ hout ω)

/-- One of the four literal inside/outside combinations. False denotes
the first raw source and true the second. -/
def sewnField {Λ : Finset Site} (inside : Finset Site) (ω : Sources Λ)
    (inner outer : Bool) : ↥Λ → Bool := fun v =>
  if (v : Site) ∈ inside then (if inner then ω.2 v else ω.1 v)
  else (if outer then ω.2 v else ω.1 v)

theorem sewnField_seamSwap {Λ : Finset Site} (inside : Finset Site) (ω : Sources Λ)
    (a b : Bool) : sewnField inside (seamSwap inside ω) a b = sewnField inside ω (!a) b := by
  funext v
  by_cases hv : (v : Site) ∈ inside <;> cases a <;> cases b <;>
    simp [sewnField, seamSwap, hv]

theorem sewnField_sourceSwap {Λ : Finset Site} (inside : Finset Site) (ω : Sources Λ)
    (a b : Bool) : sewnField inside ω.swap a b = sewnField inside ω (!a) (!b) := by
  funext v
  by_cases hv : (v : Site) ∈ inside <;> cases a <;> cases b <;>
    simp [sewnField, hv]

/-- The source's witness sharing pattern: two source-indexed inner
necklaces and two source-indexed outer necklaces work in all four
combinations. R contains the geometric screen/necklace/connection tests.
No canonical witness is selected, so nonunique necklaces cause no issue. -/
def FourWaySuccess {Λ : Finset Site} {Inner Outer : Type*}
    (inside : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop)
    (ω : Sources Λ) : Prop :=
  ∃ inner : Bool → Inner, ∃ outer : Bool → Outer,
    ∀ a b, R (inner a) (outer b) (sewnField inside ω a b)

theorem fourWaySuccess_seamSwap_iff {Λ : Finset Site} {Inner Outer : Type*}
    (inside : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop) (ω : Sources Λ) :
    FourWaySuccess inside R (seamSwap inside ω) ↔ FourWaySuccess inside R ω := by
  have forward (η : Sources Λ) : FourWaySuccess inside R η →
      FourWaySuccess inside R (seamSwap inside η) := by
    rintro ⟨inn, out, h⟩
    refine ⟨fun a => inn (!a), out, ?_⟩
    intro a b
    rw [sewnField_seamSwap]
    exact h (!a) b
  constructor
  · intro h
    simpa only [seamSwap_involutive inside ω] using forward _ h
  · exact forward ω

theorem fourWaySuccess_sourceSwap_iff {Λ : Finset Site} {Inner Outer : Type*}
    (inside : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop) (ω : Sources Λ) :
    FourWaySuccess inside R ω.swap ↔ FourWaySuccess inside R ω := by
  have forward (η : Sources Λ) : FourWaySuccess inside R η →
      FourWaySuccess inside R η.swap := by
    rintro ⟨inn, out, h⟩
    refine ⟨fun a => inn (!a), fun b => out (!b), ?_⟩
    intro a b
    rw [sewnField_sourceSwap]
    exact h (!a) (!b)
  constructor
  · intro h
    exact forward _ h
  · exact forward ω

noncomputable def fourWayTest {Λ : Finset Site} {Inner Outer : Type*}
    (inside : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop)
    (ω : Sources Λ) : Bool := decide (FourWaySuccess inside R ω)

theorem fourWayTest_seamSwap {Λ : Finset Site} {Inner Outer : Type*}
    (inside : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop) (ω : Sources Λ) :
    fourWayTest inside R (seamSwap inside ω) = fourWayTest inside R ω := by
  simp only [fourWayTest, fourWaySuccess_seamSwap_iff]

theorem fourWayTest_sourceSwap {Λ : Finset Site} {Inner Outer : Type*}
    (inside : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop) (ω : Sources Λ) :
    fourWayTest inside R ω.swap = fourWayTest inside R ω := by
  simp only [fourWayTest, fourWaySuccess_sourceSwap_iff]

/-- Locality of the necklace/screens/connector relation in its buffered
trial support is the remaining geometric support certificate. -/
def SupportedSeamRelation {Λ : Finset Site} {Inner Outer : Type*}
    (D : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop) : Prop :=
  ∀ inn out ω η, (∀ v : ↥Λ, (v : Site) ∈ D → ω v = η v) →
    (R inn out ω ↔ R inn out η)

theorem fourWayTest_supported {Λ : Finset Site} {Inner Outer : Type*}
    (D inside : Finset Site) (R : Inner → Outer → (↥Λ → Bool) → Prop)
    (hR : SupportedSeamRelation D R) : SupportedSourceTest D (fourWayTest inside R) := by
  intro ω η h
  have hfield (a b : Bool) : ∀ v : ↥Λ, (v : Site) ∈ D →
      sewnField inside ω a b v = sewnField inside η a b v := by
    intro v hv
    obtain ⟨h₁, h₂⟩ := h v hv
    simp only [sewnField, h₁, h₂]
  have heq : FourWaySuccess inside R ω ↔ FourWaySuccess inside R η := by
    constructor
    · rintro ⟨inn, out, hw⟩
      exact ⟨inn, out, fun a b => (hR _ _ _ _ (hfield a b)).mp (hw a b)⟩
    · rintro ⟨inn, out, hw⟩
      exact ⟨inn, out, fun a b => (hR _ _ _ _ (hfield a b)).mpr (hw a b)⟩
  simp only [fourWayTest, heq]

/-- Invariance of every trial test under the adaptive seam map is now a
theorem from the all-four witness pattern and disjoint nested supports. -/
theorem fourWay_trials_invariant {Λ : Finset Site} {I Inner Outer : Type*}
    (inside support : I → Finset Site) (R : I → Inner → Outer → (↥Λ → Bool) → Prop)
    (hR : ∀ i, SupportedSeamRelation (support i) (R i))
    (hnested : ∀ i j, j = i ∨ support j ⊆ inside i ∨ Disjoint (support j) (inside i)) :
    ∀ i ω, fourWayTest (inside i) (R i) ω = true →
      ∀ j, fourWayTest (inside j) (R j) (seamSwap (inside i) ω) =
        fourWayTest (inside j) (R j) ω := by
  exact trial_invariance_of_nested_supports (fun i => fourWayTest (inside i) (R i))
    inside support (fun i => fourWayTest_supported _ _ _ (hR i))
    (fun i => fourWayTest_sourceSwap _ _) (fun i => fourWayTest_seamSwap _ _) hnested

theorem sourceLaw_swap_expect {Λ : Finset Site} (f : Sources Λ → ℝ) :
    (sourceLaw Λ).expect (fun ω => f ω.swap) = (sourceLaw Λ).expect f := by
  unfold sourceLaw
  rw [FiniteLaw.expect_prod, FiniteLaw.expect_prod]
  exact FiniteLaw.expect_comm _ _ _

theorem selector_source_swap {Λ : Finset Site} {I : Type*}
    (success : I → Sources Λ → Bool) (trials : List I)
    (hsymmetric : ∀ i ω, success i ω.swap = success i ω) (ω : Sources Λ) :
    AdaptiveExchange.select success trials ω.swap =
      AdaptiveExchange.select success trials ω := by
  unfold AdaptiveExchange.select
  congr 1
  funext i
  exact hsymmetric i ω

/-- E itself need not be invariant under a selected seam. Only swapping
the two entire source fields is used in this probability equality. -/
theorem source_failure_symmetry {Λ : Finset Site} {I : Type*}
    (success : I → Sources Λ → Bool) (trials : List I)
    (hsymmetric : ∀ i ω, success i ω.swap = success i ω) (mic sq : Probe) :
    probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select success trials ω = none ∧
        SourceE mic sq (complete ω.2) (complete ω.1)) =
      probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select success trials ω = none ∧
        SourceE mic sq (complete ω.1) (complete ω.2)) := by
  let f := fun ω : Sources Λ => indicator
    (AdaptiveExchange.select success trials ω = none ∧
      SourceE mic sq (complete ω.1) (complete ω.2))
  calc
    _ = (sourceLaw Λ).expect (fun ω => f ω.swap) := by
      apply FiniteLaw.expect_congr
      intro ω
      simp only [f, selector_source_swap success trials hsymmetric]
      rfl
    _ = _ := sourceLaw_swap_expect f

/-- The finite one-trial and disqualification inequalities now bound the
sum of the two oriented source-failure probabilities used by sewing. -/
theorem oriented_source_many_trial_bound {Λ : Finset Site} {n : ℕ}
    (mic sq : Probe) (success : Fin n → Sources Λ → Bool)
    (hsymmetric : ∀ i ω, success i ω.swap = success i ω)
    (bad : Fin n → Sources Λ → Prop) (C C₀ ρ a : ℝ)
    (hC : 0 ≤ C) (hn : 0 < n)
    (oneTrial : ∀ j,
      probability (sourceLaw Λ) (fun ω =>
        SourceE mic sq (complete ω.1) (complete ω.2) ∧
        (∀ i, success i ω = false) ∧ ¬ bad j ω) ≤
      C * probability (sourceLaw Λ) (fun ω =>
        SourceE mic sq (complete ω.1) (complete ω.2) ∧
        success j ω = true ∧ ∀ i, i ≠ j → success i ω = false))
    (necessary : probability (sourceLaw Λ)
      (fun ω => SourceE mic sq (complete ω.1) (complete ω.2)) ≤ C₀ * a)
    (disqualification : ∀ j, probability (sourceLaw Λ) (fun ω =>
      SourceE mic sq (complete ω.1) (complete ω.2) ∧ bad j ω) ≤ ρ * a) :
    2 * (probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select success (List.finRange n) ω = none ∧
        SourceE mic sq (complete ω.1) (complete ω.2)) +
      probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select success (List.finRange n) ω = none ∧
        SourceE mic sq (complete ω.2) (complete ω.1))) ≤
      4 * (ρ + C * C₀ / (n : ℝ)) * a := by
  rw [source_failure_symmetry success (List.finRange n) hsymmetric mic sq]
  have h := source_many_trial_bound mic sq success bad C C₀ ρ a hC hn
    oneTrial necessary disqualification
  have h' : probability (sourceLaw Λ) (fun ω =>
      AdaptiveExchange.select success (List.finRange n) ω = none ∧
        SourceE mic sq (complete ω.1) (complete ω.2)) ≤
      (ρ + C * C₀ / (n : ℝ)) * a := by
    simpa only [and_comm] using h
  linarith

#print axioms sourceLaw_swap_expect
#print axioms fourWay_trials_invariant
#print axioms source_failure_symmetry
#print axioms oriented_source_many_trial_bound

end ExceptionalTimes.PairSquareSewing
