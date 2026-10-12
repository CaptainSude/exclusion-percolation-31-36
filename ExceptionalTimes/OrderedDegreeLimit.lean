import ExceptionalTimes.OrderedGoodSewing
import ExceptionalTimes.OrderedBadForestLimit
import ExceptionalTimes.MovingWeightedLimit
import ExceptionalTimes.WordProductBridge
import ExceptionalTimes.WordForestGeometry

/-! Fixed-degree integration of the actual common-square sewing estimate.
The pointwise forest domination is separated as an analytic argument
here and will be discharged by the actual dyadic forest envelope. -/
open Filter
open scoped Classical BigOperators Topology
namespace ExceptionalTimes.OrderedDegreeLimit
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PairSquareSewing Source06Specialization IndependentAnnulusInput
open LocalDimerCalibration InsertionCounting OrderedDimerCoefficients
open FixedMeshSelectedForest UnitReferenceCover OrderedGoodSewing
open ForestSelectionIntegral EffectiveDimerInsertion
open CanonicalSpatialProduct DimerExpansion

theorem coefficient_ordered_sum {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R n : ℕ) (phase : Bool) (k : ℕ)
    (hn : T.maxLevel≤n) (hsupport : testSupport hplane T n⊆box R n)
    (rule : Rule) (outer : (Fin q×Bool→Bool)→ℝ) :
    scaledCoefficient rule
      (fun h => outer (fun qt => T.test n qt.1
        (canonicalBackground (slot phase (box R n)) (pairCoordinates.symm h) qt.2)))
      ((mesh n)^2/localS rule n) k=
      (k.factorial:ℝ)⁻¹*∑o : orders R phase k n,
        (mesh n)^(2*k)*normalizedTerm hplane T R phase k n rule outer o := by
  have hcover : ∀v∈testSupport hplane T n,∃be,slot phase (box R n) be=v :=
    fun v hv => slot_covers phase (box R n) v (hsupport hv)
  have hh := scaledCoefficient_ordered (slot phase (box R n)) (testSupport hplane T n)
    hcover rule k (mesh n) (localS rule n)
    (fun ξ => outer (fun qt => T.test n qt.1 (ξ qt.2)))
    (fun ω η hag => congrArg outer (test_local hplane T n hn ω η hag))
  apply hh.trans
  calc
    _=(mesh n)^(2*k)/(k.factorial:ℝ)*
        (∑o : orders R phase k n,normalizedTerm hplane T R phase k n rule outer o) := by
      apply congrArg (fun x : ℝ => (mesh n)^(2*k)/(k.factorial:ℝ)*x)
      apply Finset.sum_congr
      · ext o
        simp only [Finset.mem_univ]
      · intro o _
        rfl
    _=_ := by
      conv_rhs => rw [←Finset.mul_sum]
      ring

#print axioms coefficient_ordered_sum

theorem difference_ordered_sum {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R n : ℕ) (phase : Bool) (k : ℕ)
    (hn : T.maxLevel≤n) (hsupport : testSupport hplane T n⊆box R n)
    (outer : (Fin q×Bool→Bool)→ℝ) :
    scaledCoefficient .canonical
      (fun h => outer (fun qt => T.test n qt.1
        (canonicalBackground (slot phase (box R n)) (pairCoordinates.symm h) qt.2)))
      ((mesh n)^2/localS .canonical n) k-
    scaledCoefficient .refresh
      (fun h => outer (fun qt => T.test n qt.1
        (canonicalBackground (slot phase (box R n)) (pairCoordinates.symm h) qt.2)))
      ((mesh n)^2/localS .refresh n) k=
      (k.factorial:ℝ)⁻¹*∑o : orders R phase k n,(mesh n)^(2*k)*
        (normalizedTerm hplane T R phase k n .canonical outer o-
         normalizedTerm hplane T R phase k n .refresh outer o) := by
  rw [coefficient_ordered_sum hplane T R n phase k hn hsupport,
      coefficient_ordered_sum hplane T R n phase k hn hsupport]
  simp only [mul_sub,Finset.sum_sub_distrib]

#print axioms difference_ordered_sum

theorem tendsto_of_forest_domination {q k : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R : ℕ) (phase : Bool)
    (hsupport : ∀n,testSupport hplane T n⊆box R n)
    (B : ℝ) (hseams : PublishedFixedSquareSeams B)
    (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (outer : (Fin q×Bool→Bool)→ℝ) (hout : ∀x,|outer x|≤1)
    (b : ℕ→ℝ) {κ g radius C W : ℝ}
    (hκ : 0<κ) (hg : 0<g) (hg2 : g<2) (hradius : 0<radius)
    (hC : 0≤C) (hW : 0≤W)
    (hb : ∀ᶠn in atTop,κ*mesh n≤b n)
    (hbound : ∀ᶠn in atTop,∀o : orders R phase (k+1) n,
      |normalizedTerm hplane T R phase (k+1) n .canonical outer o|+
      |normalizedTerm hplane T R phase (k+1) n .refresh outer o|≤
      W*forestTuple (k+1) (anchorSet R phase n) (mesh n) (b n) g radius C
        (T.root hplane) (anchorTuple o)) :
    Tendsto (fun n =>
      scaledCoefficient .canonical
        (fun h => outer (fun qt => T.test n qt.1
          (canonicalBackground (slot phase (box R n)) (pairCoordinates.symm h) qt.2)))
        ((mesh n)^2/localS .canonical n) (k+1)-
      scaledCoefficient .refresh
        (fun h => outer (fun qt => T.test n qt.1
          (canonicalBackground (slot phase (box R n)) (pairCoordinates.symm h) qt.2)))
        ((mesh n)^2/localS .refresh n) (k+1)) atTop (𝓝 0) := by
  obtain ⟨p,t,hpt,hgp⟩ := OrderedBadForestLimit.exists_holder_margin hg hg2
  have hbad := OrderedBadForestLimit.weighted_bad_small (k+1) (anchorSet R phase)
    (dyadicSourcePolygons T hplane) (fun i => (T.grid i).presentation hplane)
    b (fun _ => T.root hplane)
    (fun n => normalizedTerm hplane T R phase (k+1) n .canonical outer)
    (fun n => normalizedTerm hplane T R phase (k+1) n .refresh outer)
    (r:=2*((R:ℝ)+1)) 0 hκ hg.le hpt hgp hradius (by positivity) hC hW hb
    (Filter.Eventually.of_forall (fun n a ha => by
      simpa only [sub_zero] using box_anchor_physical_bound R n phase a ha)) hbound
  have hlim := MovingWeightedLimit.tendsto_weighted_difference
    (fun n (_ : orders R phase (k+1) n) => (mesh n)^(2*(k+1)))
    (fun n => normalizedTerm hplane T R phase (k+1) n .canonical outer)
    (fun n => normalizedTerm hplane T R phase (k+1) n .refresh outer)
    (fun δ n => OrderedBadForestLimit.badOrders (anchorSet R phase n) (k+1)
      (dyadicSourcePolygons T hplane) (mesh n) δ) ((121*(2*((R:ℝ)+1))^2)^(k+1))
    (Filter.Eventually.of_forall (fun n _ => pow_nonneg (mesh_pos n).le _))
    (Filter.Eventually.of_forall (fun n => ordered_mass R phase (k+1) n))
    (by
      intro δ hδ η hη
      filter_upwards [uniform_good hplane T R phase B hseams hstatic hbulk hlower harmlower
        hattach outer hout δ hδ η hη] with n hgn
      intro o ho
      apply hgn o
      intro hoi
      apply ho
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (OrderedTupleMass.mem_badOrders _ _ o).mp hoi⟩)
    hbad
  have hscaled := hlim.const_mul ((Nat.factorial (k+1):ℝ)⁻¹)
  rw [mul_zero] at hscaled
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop T.maxLevel] with n hn
  exact (difference_ordered_sum hplane T R n phase (k+1) hn (hsupport n) outer).symm

#print axioms coefficient_ordered_sum
#print axioms tendsto_of_forest_domination
end
end ExceptionalTimes.OrderedDegreeLimit
