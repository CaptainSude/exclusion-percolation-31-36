import ExceptionalTimes.SewnConnectorHarris

open Set
open scoped Classical BigOperators

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance FiniteHaar ProbeProduct

theorem sourceLaw_seamSwap_expect {Λ : Finset Site} (inside : Finset Site)
    (f : Sources Λ → ℝ) :
    (sourceLaw Λ).expect (fun ω => f (seamSwap inside ω)) = (sourceLaw Λ).expect f := by
  let e : Sources Λ ≃ Sources Λ := (seamSwap_involutive inside).toPerm
  simp only [sourceLaw_expect_eq_average]
  exact average_equiv e f

theorem sewnField_same {Λ : Finset Site} (inside : Finset Site) (ω : Sources Λ) (b : Bool) :
    sewnField inside ω b b = if b then ω.2 else ω.1 := by
  funext v
  by_cases hv : (v:Site) ∈ inside <;> cases b <;> simp [sewnField,hv]

theorem sewnField_same_expect {Λ : Finset Site} (inside : Finset Site) (b : Bool)
    (f : (↥Λ → Bool) → ℝ) :
    (sourceLaw Λ).expect (fun ω => f (sewnField inside ω b b)) = (fairSites ↥Λ).expect f := by
  simp only [sewnField_same]
  rw [sourceLaw,FiniteLaw.expect_prod]
  cases b <;> simp

/-- Every fixed inside/outside combination has exactly the original fair
site law, even if its connector crosses the seam. -/
theorem sewnField_expect {Λ : Finset Site} (inside : Finset Site) (a b : Bool)
    (f : (↥Λ → Bool) → ℝ) :
    (sourceLaw Λ).expect (fun ω => f (sewnField inside ω a b)) = (fairSites ↥Λ).expect f := by
  by_cases hab : a=b
  · subst a
    exact sewnField_same_expect inside b f
  · have hflip : (!a) = b := by cases a <;> cases b <;> simp_all
    have h := sourceLaw_seamSwap_expect inside (fun ω => f (sewnField inside ω a b))
    have h' : (sourceLaw Λ).expect (fun ω => f (sewnField inside ω b b)) =
        (sourceLaw Λ).expect (fun ω => f (sewnField inside ω a b)) := by
      simpa only [sewnField_seamSwap,hflip] using h
    exact h'.symm.trans (sewnField_same_expect inside b f)

theorem SewnConnector.probability_eq {Λ : Finset Site} (C : SewnConnector) (inside : Finset Site) :
    probability (sourceLaw Λ) (C.event inside) =
      probability (fairSites ↥Λ) (fun ω => C.quad.ColorCrossing C.color (complete ω)) := by
  unfold probability SewnConnector.event
  exact sewnField_expect (Λ := Λ) inside C.innerSource C.outerSource
    (fun ω => EnvironmentVariance.indicator (C.quad.ColorCrossing C.color (complete ω)))

def axialRectangleSites (left right bottom top : ℤ) : Finset Site :=
  (Finset.Icc left right).product (Finset.Icc bottom top)

def horizontalTrack (left right bottom top : ℤ) : GraphQuad where
  domain := axialRectangleSites left right bottom top
  firstSide := (axialRectangleSites left right bottom top).filter (fun v => v.1=left)
  secondSide := (axialRectangleSites left right bottom top).filter (fun v => v.1=right)

def verticalTrack (left right bottom top : ℤ) : GraphQuad where
  domain := axialRectangleSites left right bottom top
  firstSide := (axialRectangleSites left right bottom top).filter (fun v => v.2=bottom)
  secondSide := (axialRectangleSites left right bottom top).filter (fun v => v.2=top)

/-- Four literal radial rectangle tracks across a seam space. The inner
radius r exceeds their half-width w, so opposite-color domains have a
strict positive coordinate gap. Indices 0,2 are black and 1,3 white. -/
def cardinalTrack (r R w : ℤ) (i : Fin 4) : GraphQuad :=
  ![horizontalTrack r R (-w) w, verticalTrack (-w) w r R,
    horizontalTrack (-R) (-r) (-w) w, verticalTrack (-w) w (-R) (-r)] i

def cardinalBlack (r R w : ℤ) : Finset Site :=
  (cardinalTrack r R w 0).domain ∪ (cardinalTrack r R w 2).domain

def cardinalWhite (r R w : ℤ) : Finset Site :=
  (cardinalTrack r R w 1).domain ∪ (cardinalTrack r R w 3).domain

def cardinalSupport (r R w : ℤ) : Finset Site := cardinalBlack r R w ∪ cardinalWhite r R w

theorem cardinal_opposite_disjoint (r R w : ℤ) (hgap : w < r) :
    Disjoint (cardinalBlack r R w) (cardinalWhite r R w) := by
  apply Finset.disjoint_left.mpr
  intro v hB hW
  simp only [cardinalBlack,cardinalWhite,Finset.mem_union] at hB hW
  rcases hB with hB | hB <;> rcases hW with hW | hW <;>
    simp [cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] at hB hW <;> omega

def cardinalConnector (r R w : ℤ) (j : Fin 4 × Bool × Bool) : SewnConnector where
  quad := cardinalTrack r R w j.1
  color := decide (j.1.val % 2 = 0)
  innerSource := j.2.1
  outerSource := j.2.2

theorem cardinalConnector_fits {Λ : Finset Site} (r R w : ℤ) (hgap : w < r)
    (hΛ : cardinalSupport r R w ⊆ Λ) (j : Fin 4 × Bool × Bool) :
    (cardinalConnector r R w j).Fits Λ (cardinalWhite r R w) := by
  apply SewnConnector.fits_of_separated _ _ (cardinalBlack r R w) _
    (cardinal_opposite_disjoint r R w hgap)
    (Finset.subset_union_left.trans hΛ) (Finset.subset_union_right.trans hΛ)
  rcases j with ⟨i,a,b⟩
  fin_cases i <;> simp [cardinalConnector,cardinalBlack,cardinalWhite]

/-- A concrete sixteen-requirement seam event: the four tracks cross in
all four sewn fields. Its joint lower bound follows from ordinary single-
field crossing bounds and the proved site separation above. There is no
arm-event normalization or one-trial comparison assumption here. -/
theorem cardinal_sixteen_crossings_lower {Λ : Finset Site} (inside : Finset Site)
    (r R w : ℤ) (hgap : w < r) (hΛ : cardinalSupport r R w ⊆ Λ)
    (c : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ i : Fin 4, c ≤ probability (fairSites ↥Λ)
      (fun ω => (cardinalTrack r R w i).ColorCrossing (decide (i.val % 2 = 0)) (complete ω))) :
    c^16 ≤ probability (sourceLaw Λ)
      (fun ω => ∀ j : Fin 4 × Bool × Bool, (cardinalConnector r R w j).event inside ω) := by
  have h := sewn_connector_joint_bound (cardinalConnector r R w) inside (cardinalWhite r R w)
    (cardinalConnector_fits r R w hgap hΛ)
  have hprod : (∏ _j : Fin 4 × Bool × Bool, c) ≤
      ∏ j : Fin 4 × Bool × Bool, probability (sourceLaw Λ)
        ((cardinalConnector r R w j).event inside) := by
    apply Finset.prod_le_prod₀ (fun _ _ => hc)
    intro j _
    rw [SewnConnector.probability_eq]
    exact hlower j.1
  have hcprod : (∏ _j : Fin 4 × Bool × Bool, c) = c^16 := by simp
  rw [hcprod] at hprod
  exact hprod.trans h

#print axioms sewnField_expect
#print axioms cardinal_opposite_disjoint
#print axioms cardinal_sixteen_crossings_lower

end ExceptionalTimes.PairSquareSewing
