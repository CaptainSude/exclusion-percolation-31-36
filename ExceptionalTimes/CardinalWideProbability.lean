import ExceptionalTimes.CardinalWideStatic
import ExceptionalTimes.CardinalGuardedProbability

open Set
open scoped Classical BigOperators

namespace ExceptionalTimes.PairSquareSewing

open AnnularCollars EnvironmentVariance FiniteHaar ProbeProduct NolinCorridor

def wideGuardRequirement {Λ : Finset Site} (r R : ℤ) (w U : ℕ)
    (k : GuardIndex) (ω : Sources Λ) : Prop :=
  ColoredGuard (cardinalEndpoint (if k.1 then R else r) k.2.1) w U
    (decide (k.2.1.val % 2=0)) (complete (if k.2.2 then ω.2 else ω.1))

def wideCardinalRequirement {Λ : Finset Site} (r R : ℤ) (w U : ℕ) (inside : Finset Site)
    (j : ConnectorIndex ⊕ GuardIndex) (ω : Sources Λ) : Prop :=
  match j with
  | .inl j => (cardinalConnector r R w j).event inside ω
  | .inr k => wideGuardRequirement r R w U k ω

theorem wideGuardRequirement_mono {Λ : Finset Site} (r R : ℤ) (w U : ℕ)
    (hwidth : 2*U < r) (hrR : r ≤ R)
    (hΛ : cardinalSupport (r-U) (R+U) U ⊆ Λ)
    (k : GuardIndex) {ω η : Sources Λ} (hωη : ω ≤ η) :
    wideGuardRequirement r R w U k (polarizeSources (cardinalWhite (r-U) (R+U) U) ω) →
    wideGuardRequirement r R w U k (polarizeSources (cardinalWhite (r-U) (R+U) U) η) := by
  rintro ⟨C,hC⟩
  refine ⟨C,?_⟩
  intro z hz
  have ht : (if k.1 then R else r)=r ∨ (if k.1 then R else r)=R := by cases k.1 <;> simp
  have hzdom := cardinalEndpoint_wide_box_subset r R U hrR k.2.1 _ ht
    (shiftedCircuit_inside _ C hz)
  have hfit := cardinalConnector_fits (r-U) (R+U) U (by omega) hΛ (k.2.1,k.2.2,k.2.2)
  have hs := sewn_favorable_color ∅ (cardinalWhite (r-U) (R+U) U)
    k.2.2 k.2.2 (decide (k.2.1.val % 2=0)) hωη (hfit.1 hzdom) (hfit.2 z hzdom)
  simpa only [sewnField_same] using hs (by simpa only [sewnField_same] using hC z hz)

theorem wideGuardRequirement_probability {Λ : Finset Site} (r R : ℤ) (w U : ℕ)
    (k : GuardIndex) :
    probability (sourceLaw Λ) (wideGuardRequirement r R w U k) =
      probability (fairSites ↥Λ) (fun ω =>
        ColoredGuard (cardinalEndpoint (if k.1 then R else r) k.2.1) w U
          (decide (k.2.1.val % 2=0)) (complete ω)) :=
  sourceLaw_raw_probability (Λ := Λ) k.2.2
    (fun ω => ColoredGuard (cardinalEndpoint (if k.1 then R else r) k.2.1) w U
      (decide (k.2.1.val % 2=0)) (complete ω))

theorem wideCardinalRequirement_mono {Λ : Finset Site} (r R : ℤ) (w U : ℕ)
    (inside : Finset Site) (hwU : w ≤ U) (hwidth : 2*U < r) (hrR : r ≤ R)
    (hΛ : cardinalSupport (r-U) (R+U) U ⊆ Λ)
    (j : ConnectorIndex ⊕ GuardIndex) {ω η : Sources Λ} (hωη : ω ≤ η) :
    wideCardinalRequirement r R w U inside j (polarizeSources (cardinalWhite (r-U) (R+U) U) ω) →
    wideCardinalRequirement r R w U inside j (polarizeSources (cardinalWhite (r-U) (R+U) U) η) := by
  cases j with
  | inr k => exact wideGuardRequirement_mono r R w U hwidth hrR hΛ k hωη
  | inl j =>
    apply SewnConnector.event_polarized_mono _ _ _ _ hωη
    have hfit := cardinalConnector_fits (r-U) (R+U) U (by omega) hΛ j
    refine ⟨(cardinalTrack_subset_wide r R w U hwU j.1).trans hfit.1,?_⟩
    intro z hz
    exact hfit.2 z (cardinalTrack_subset_wide r R w U hwU j.1 hz)

theorem wide_cardinal_probability_lower {Λ : Finset Site} (r R : ℤ) (w U : ℕ)
    (inside : Finset Site) (hwU : w ≤ U) (hwidth : 2*U < r) (hrR : r ≤ R)
    (hΛ : cardinalSupport (r-U) (R+U) U ⊆ Λ) (c : ℝ) (hc : 0 ≤ c)
    (htrack : ∀ i : Fin 4, c ≤ probability (fairSites ↥Λ)
      (fun ω => (cardinalTrack r R w i).ColorCrossing (decide (i.val % 2=0)) (complete ω)))
    (hguard : ∀ t : ℤ, t=r ∨ t=R → ∀ i : Fin 4,
      c ≤ probability (fairSites ↥Λ) (fun ω =>
        ColoredGuard (cardinalEndpoint t i) w U (decide (i.val % 2=0)) (complete ω))) :
    c^32 ≤ probability (sourceLaw Λ)
      (fun ω => ∀ j : ConnectorIndex ⊕ GuardIndex, wideCardinalRequirement r R w U inside j ω) := by
  have h := sourceLaw_favorable_joint (wideCardinalRequirement r R w U inside)
    (cardinalWhite (r-U) (R+U) U)
    (fun j _ _ h => wideCardinalRequirement_mono r R w U inside hwU hwidth hrR hΛ j h)
  have hprod : (∏ _j : ConnectorIndex ⊕ GuardIndex, c) ≤
      ∏ j : ConnectorIndex ⊕ GuardIndex,
        probability (sourceLaw Λ) (wideCardinalRequirement r R w U inside j) := by
    apply Finset.prod_le_prod₀ (fun _ _ => hc)
    intro j _
    cases j with
    | inl j =>
      change c ≤ probability (sourceLaw Λ) ((cardinalConnector r R w j).event inside)
      rw [SewnConnector.probability_eq]
      exact htrack j.1
    | inr k =>
      change c ≤ probability (sourceLaw Λ) (wideGuardRequirement r R w U k)
      rw [wideGuardRequirement_probability]
      apply hguard
      cases k.1 <;> simp
  have hcprod : (∏ _j : ConnectorIndex ⊕ GuardIndex, c)=c^32 := by
    simp [ConnectorIndex,GuardIndex]
  rw [hcprod] at hprod
  exact hprod.trans h

theorem cardinalMap_rectangle_subset_wide (r : ℤ) (w U M : ℕ)
    (hw : 1 ≤ w) (hwU : w ≤ U) (i : Fin 4) {z : Site}
    (hz : z ∈ rectangle M (2*w)) :
    cardinalMap r w i z ∈ (cardinalTrack (r-U) (r+M-2+U) U i).domain := by
  simp only [rectangle,Finset.mem_product,Finset.mem_Icc] at hz
  fin_cases i <;>
    simp [cardinalMap,cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] <;> omega

/-- A genuine finite guarded connector event, with its positive lower
bound derived only from the already audited RSW, one-arm upper bound,
and planar circuit duality. This event is still one component of a
successful trial; it does not include the sleeve necklace construction. -/
theorem wide_cardinal_lower_of_published
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : PublishedAnnularOneArmUpper B₀ C β) (hβ : 0 < β) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ (w : ℕ), 1 ≤ w → B₀ ≤ w → ∀ (r : ℤ), 2*(K*w+1) < r →
        ∀ (Λ inside : Finset Site),
          cardinalSupport (r-(K*w+1)) (r+k*(2*w)-2+(K*w+1)) (K*w+1) ⊆ Λ →
          c^32 ≤ probability (sourceLaw Λ) (fun ω =>
            ∀ j : ConnectorIndex ⊕ GuardIndex,
              wideCardinalRequirement r (r+k*(2*w)-2) w (K*w+1) inside j ω) := by
  obtain ⟨K,hK,hguard⟩ := coloredGuard_lower_of_published boundaryInput hupper hβ
  refine ⟨K,hK,?_⟩
  intro k hk
  obtain ⟨δ,hδ,htrack⟩ := cardinal_track_lower_of_RSW hRSW k hk
  let c : ℝ := min δ (1/2)
  refine ⟨c,lt_min hδ (by norm_num),?_⟩
  intro w hw hBw r hwidth Λ inside hΛ
  have hwU : w ≤ K*w+1 := by nlinarith
  have hrR : r ≤ r+(k*(2*w):ℕ)-2 := by
    have hfour : 4 ≤ k*(2*w) := by nlinarith
    omega
  apply wide_cardinal_probability_lower r (r+k*(2*w)-2) w (K*w+1) inside hwU
    hwidth hrR hΛ c (le_of_lt (lt_min hδ (by norm_num)))
  · intro i
    apply (min_le_left δ (1/2)).trans (htrack w hw r Λ i ?_ _)
    intro z hz
    have hzdom := cardinalMap_rectangle_subset_wide r w (K*w+1) (k*(2*w)) hw hwU i hz
    exact (cardinalConnector_fits (r-(K*w+1)) (r+k*(2*w)-2+(K*w+1)) (K*w+1)
      (by omega) hΛ (i,false,false)).1 hzdom
  · intro t ht i
    apply (min_le_right δ (1/2)).trans (hguard w hw hBw (cardinalEndpoint t i) Λ ?_ _)
    intro z hz
    have hz' : cardinalEndpoint t i+z-cardinalEndpoint t i ∈ latticeBox (K*w+1) := by
      simpa only [add_sub_cancel_left] using hz
    have hzdom := cardinalEndpoint_wide_box_subset r (r+k*(2*w)-2) (K*w+1) hrR i t ht hz'
    exact (cardinalConnector_fits (r-(K*w+1)) (r+k*(2*w)-2+(K*w+1)) (K*w+1)
      (by omega) hΛ (i,false,false)).1 hzdom

#print axioms wide_cardinal_lower_of_published

end ExceptionalTimes.PairSquareSewing
