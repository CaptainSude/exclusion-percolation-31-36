import ExceptionalTimes.CardinalGuardedSeam

open Set
open scoped Classical BigOperators

namespace ExceptionalTimes.PairSquareSewing

open AnnularCollars EnvironmentVariance FiniteHaar ProbeProduct

/-- A literal monochromatic surrounding guard, translated to its
cardinal endpoint patch. -/
def CardinalGuard (t : ℤ) (w : ℕ) (i : Fin 4) (ω : Configuration) : Prop :=
  ∃ C : SurroundingCircuit w (2*w),
    ∀ z ∈ (shiftedCircuit (cardinalEndpoint t i) C).support, ω z=decide (i.val % 2=0)

abbrev GuardIndex := Bool × Fin 4 × Bool
abbrev ConnectorIndex := Fin 4 × Bool × Bool

def cardinalGuardRequirement {Λ : Finset Site} (r R : ℤ) (w : ℕ)
    (k : GuardIndex) (ω : Sources Λ) : Prop :=
  CardinalGuard (if k.1 then R else r) w k.2.1
    (complete (if k.2.2 then ω.2 else ω.1))

def cardinalAugmentedRequirement {Λ : Finset Site} (r R : ℤ) (w : ℕ) (inside : Finset Site)
    (j : ConnectorIndex ⊕ GuardIndex) (ω : Sources Λ) : Prop :=
  match j with
  | .inl j => (cardinalConnector r R w j).event inside ω
  | .inr k => cardinalGuardRequirement r R w k ω

theorem sewn_favorable_color {Λ : Finset Site} (inside white : Finset Site)
    (a b color : Bool) {ω η : Sources Λ} (h : ω ≤ η) {z : Site}
    (hzΛ : z ∈ Λ) (hwhite : z ∈ white ↔ color=false)
    (hz : complete (sewnField inside (polarizeSources white ω) a b) z=color) :
    complete (sewnField inside (polarizeSources white η) a b) z=color := by
  have hbit := sewnField_mono inside a b h ⟨z,hzΛ⟩
  simp only [complete,hzΛ,dite_eq_left,sewnField_polarize] at hz ⊢
  cases hc : color
  · have hw : z ∈ white := hwhite.mpr hc
    simp only [hw,ite_true,hc,Bool.not_eq_false_eq_eq_true] at hz ⊢
    rw [hz] at hbit
    exact top_le_iff.mp hbit
  · have hw : z ∉ white := fun hw => by simpa [hc] using hwhite.mp hw
    simp only [hw,ite_false,hc] at hz ⊢
    rw [hz] at hbit
    exact top_le_iff.mp hbit

theorem cardinalGuardRequirement_mono {Λ : Finset Site} (r R : ℤ) (w : ℕ)
    (hwidth : 4*w < r) (hrR : r ≤ R)
    (hΛ : cardinalSupport (r-2*w) (R+2*w) (2*w) ⊆ Λ)
    (k : GuardIndex) {ω η : Sources Λ} (hωη : ω ≤ η) :
    cardinalGuardRequirement r R w k
      (polarizeSources (cardinalWhite (r-2*w) (R+2*w) (2*w)) ω) →
    cardinalGuardRequirement r R w k
      (polarizeSources (cardinalWhite (r-2*w) (R+2*w) (2*w)) η) := by
  rintro ⟨C,hC⟩
  refine ⟨C,?_⟩
  intro z hz
  have ht : (if k.1 then R else r)=r ∨ (if k.1 then R else r)=R := by cases k.1 <;> simp
  have hzdom := cardinalEndpoint_box_subset r R w hrR k.2.1 _ ht
    (shiftedCircuit_inside _ C hz)
  have hfit := cardinalConnector_fits (r-2*w) (R+2*w) (2*w) (by omega) hΛ
    (k.2.1,k.2.2,k.2.2)
  have hzΛ := hfit.1 hzdom
  have hw := hfit.2 z hzdom
  have hs := sewn_favorable_color ∅ (cardinalWhite (r-2*w) (R+2*w) (2*w))
    k.2.2 k.2.2 (decide (k.2.1.val % 2=0)) hωη hzΛ hw
  simpa only [sewnField_same] using hs (by simpa only [sewnField_same] using hC z hz)

theorem sourceLaw_raw_probability {Λ : Finset Site} (b : Bool)
    (E : (↥Λ → Bool) → Prop) :
    probability (sourceLaw Λ) (fun ω => E (if b then ω.2 else ω.1)) =
      probability (fairSites ↥Λ) E := by
  unfold probability
  rw [sourceLaw,FiniteLaw.expect_prod]
  cases b <;> simp

theorem cardinalGuardRequirement_probability {Λ : Finset Site} (r R : ℤ) (w : ℕ)
    (k : GuardIndex) :
    probability (sourceLaw Λ) (cardinalGuardRequirement r R w k) =
      probability (fairSites ↥Λ) (fun ω =>
        CardinalGuard (if k.1 then R else r) w k.2.1 (complete ω)) :=
  sourceLaw_raw_probability (Λ := Λ) k.2.2
    (fun ω => CardinalGuard (if k.1 then R else r) w k.2.1 (complete ω))

theorem sourceLaw_favorable_joint {Λ : Finset Site} {I : Type*} [Fintype I]
    (E : I → Sources Λ → Prop) (white : Finset Site)
    (hmono : ∀ i {ω η}, ω ≤ η → E i (polarizeSources white ω) → E i (polarizeSources white η)) :
    (∏ i, probability (sourceLaw Λ) (E i)) ≤
      probability (sourceLaw Λ) (fun ω => ∀ i, E i ω) := by
  classical
  let f (i : I) (ω : Sources Λ) := indicator (E i (polarizeSources white ω))
  have hf (i : I) : Monotone (f i) := by
    intro ω η hωη
    by_cases hω : E i (polarizeSources white ω)
    · have hη := hmono i hωη hω
      simp [f,EnvironmentVariance.indicator,hω,hη]
    · simpa only [f,EnvironmentVariance.indicator,hω,ite_false] using indicator_nonneg
        (E i (polarizeSources white η))
  have h := uniform_harris_finite_product Finset.univ f (fun i _ => hf i)
    (fun i _ ω => indicator_nonneg _)
  have hprob (i : I) : average (f i) = probability (sourceLaw Λ) (E i) := by
    rw [←sourceLaw_polarize_probability white]
    simp only [probability,sourceLaw_expect_eq_average,f]
  have hprod : average (fun ω => ∏ i, f i ω) =
      probability (sourceLaw Λ) (fun ω => ∀ i, E i ω) := by
    rw [←sourceLaw_polarize_probability white]
    simp only [probability,sourceLaw_expect_eq_average,f,ProbeProduct.indicator_forall]
  simpa only [hprob,hprod] using h

theorem cardinalAugmentedRequirement_mono {Λ : Finset Site} (r R : ℤ) (w : ℕ) (inside : Finset Site)
    (hwidth : 4*w < r) (hrR : r ≤ R)
    (hΛ : cardinalSupport (r-2*w) (R+2*w) (2*w) ⊆ Λ)
    (j : ConnectorIndex ⊕ GuardIndex) {ω η : Sources Λ} (hωη : ω ≤ η) :
    cardinalAugmentedRequirement r R w inside j
      (polarizeSources (cardinalWhite (r-2*w) (R+2*w) (2*w)) ω) →
    cardinalAugmentedRequirement r R w inside j
      (polarizeSources (cardinalWhite (r-2*w) (R+2*w) (2*w)) η) := by
  cases j with
  | inr k => exact cardinalGuardRequirement_mono r R w hwidth hrR hΛ k hωη
  | inl j =>
    apply SewnConnector.event_polarized_mono _ _ _ _ hωη
    have hfit := cardinalConnector_fits (r-2*w) (R+2*w) (2*w) (by omega) hΛ j
    refine ⟨?_,?_⟩
    · exact (cardinalTrack_subset_enlarged r R w j.1).trans hfit.1
    · intro z hz
      exact hfit.2 z (cardinalTrack_subset_enlarged r R w j.1 hz)

/-- A finite, shared-source guarded seam event has the product lower
bound supplied by Harris. The assumptions are ordinary one-field track
and surrounding-circuit probabilities. This does not assert a sleeve
event, retained-arm comparison, or any arm-normalized trial bound. -/
theorem cardinal_guarded_probability_lower {Λ : Finset Site} (r R : ℤ) (w : ℕ) (inside : Finset Site)
    (hwidth : 4*w < r) (hrR : r ≤ R)
    (hΛ : cardinalSupport (r-2*w) (R+2*w) (2*w) ⊆ Λ) (c : ℝ) (hc : 0 ≤ c)
    (htrack : ∀ i : Fin 4, c ≤ probability (fairSites ↥Λ)
      (fun ω => (cardinalTrack r R w i).ColorCrossing (decide (i.val % 2=0)) (complete ω)))
    (hguard : ∀ t : ℤ, t=r ∨ t=R → ∀ i : Fin 4,
      c ≤ probability (fairSites ↥Λ) (fun ω => CardinalGuard t w i (complete ω))) :
    c^32 ≤ probability (sourceLaw Λ)
      (fun ω => ∀ j : ConnectorIndex ⊕ GuardIndex, cardinalAugmentedRequirement r R w inside j ω) := by
  have h := sourceLaw_favorable_joint (cardinalAugmentedRequirement r R w inside)
    (cardinalWhite (r-2*w) (R+2*w) (2*w))
    (fun j _ _ h => cardinalAugmentedRequirement_mono r R w inside hwidth hrR hΛ j h)
  have hprod : (∏ _j : ConnectorIndex ⊕ GuardIndex, c) ≤
      ∏ j : ConnectorIndex ⊕ GuardIndex,
        probability (sourceLaw Λ) (cardinalAugmentedRequirement r R w inside j) := by
    apply Finset.prod_le_prod₀ (fun _ _ => hc)
    intro j _
    cases j with
    | inl j =>
      change c ≤ probability (sourceLaw Λ) ((cardinalConnector r R w j).event inside)
      rw [SewnConnector.probability_eq]
      exact htrack j.1
    | inr k =>
      change c ≤ probability (sourceLaw Λ) (cardinalGuardRequirement r R w k)
      rw [cardinalGuardRequirement_probability]
      apply hguard
      cases k.1 <;> simp
  have hcprod : (∏ _j : ConnectorIndex ⊕ GuardIndex, c)=c^32 := by
    simp [ConnectorIndex,GuardIndex]
  rw [hcprod] at hprod
  exact hprod.trans h

#print axioms cardinalGuardRequirement_mono
#print axioms cardinal_guarded_probability_lower

end ExceptionalTimes.PairSquareSewing

