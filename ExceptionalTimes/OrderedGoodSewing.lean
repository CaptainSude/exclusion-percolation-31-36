import ExceptionalTimes.OrderedDimerCoefficients
import ExceptionalTimes.OrderedTupleMass

/-! The concrete good-tuple comparison for the ordered coefficients of
the positive-orientation matching on a fixed physical box. -/
open Filter
open scoped Classical BigOperators Topology
namespace ExceptionalTimes.OrderedGoodSewing
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open PairSquareSewing Source06Specialization IndependentAnnulusInput
open LocalDimerCalibration InsertionCounting OrderedDimerCoefficients
open FixedMeshSelectedForest UnitReferenceCover

abbrev box (R n : ℕ) : Finset Site := latticeBox (R*2^n)
abbrev anchorSet (R : ℕ) (phase : Bool) (n : ℕ) := anchors phase (box R n)
abbrev orders (R : ℕ) (phase : Bool) (k n : ℕ) := OrderedSelections (anchorSet R phase n) k

def normalizedTerm {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R : ℕ) (phase : Bool) (k n : ℕ)
    (rule : Rule) (outer : (Fin q×Bool→Bool)→ℝ) (o : orders R phase k n) : ℝ :=
  fullCoefficient (testSupport hplane T n) (orderedEndpoint (slot phase (box R n)) o)
    (fun _ => rule) (fun ξ => outer (fun qt => T.test n qt.1 (ξ qt.2)))/(localS rule n)^k

def badOrders {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R : ℕ) (phase : Bool) (k : ℕ) (δ : ℝ) (n : ℕ) :
    Finset (orders R phase k n) :=
  OrderedTupleMass.badOrders k (LatticeBoundaryMass.polygonBadTuples (anchorSet R phase n) k
    (dyadicSourcePolygons T hplane) (mesh n) δ)

theorem support_member {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (n : ℕ) (i : Fin q) :
    ((T.grid i).meshPolygon hplane n).support⊆testSupport hplane T n := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩

theorem uniform_good {q k : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (R : ℕ) (phase : Bool) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) (hattach : UnitStaticAttachment.PublishedUnitAttachment B)
    (outer : (Fin q×Bool→Bool)→ℝ) (hout : ∀c,|outer c|≤1) :
    ∀δ : ℝ,0<δ→∀η : ℝ,0<η→∀ᶠn in atTop,∀o : orders R phase (k+1) n,
      o∉badOrders hplane T R phase (k+1) δ n→
      |normalizedTerm hplane T R phase (k+1) n .canonical outer o-
       normalizedTerm hplane T R phase (k+1) n .refresh outer o|<η := by
  intro δ hδ η hη
  obtain ⟨N,hN⟩ := uniform_good_tuple_normalized_limit (k:=k) T hplane 0
    (2*((R:ℝ)+1)) δ hδ B hseams hstatic hbulk hlower harmlower hattach η hη
  filter_upwards [eventually_ge_atTop N] with n hn
  intro o ho
  apply hN n hn (anchorSet R phase n)
    (fun a ha => by simpa only [sub_zero] using box_anchor_physical_bound R n phase a ha)
    (anchorTuple o)
  · exact fun h => ho ((OrderedTupleMass.mem_badOrders _ _ o).mpr h)
  · intro j
    simp only [orderedEndpoint_apply,slot_zero]
  · intro j
    simp only [orderedEndpoint_apply,slot_one]
  · exact support_member hplane T n
  · exact hout

theorem ordered_mass (R : ℕ) (phase : Bool) (k n : ℕ) :
    (∑ _o : orders R phase k n,(mesh n)^(2*k))≤
      (121*(2*((R:ℝ)+1))^2)^k := by
  have hm : mesh n≤1 := by
    unfold mesh
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hr : mesh n≤2*((R:ℝ)+1) := by nlinarith [Nat.cast_nonneg (α:=ℝ) R]
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using
    OrderedTupleMass.scaled_ordered_mass k (anchorSet R phase n) 0 (mesh_pos n) hr
      (fun a ha => by simpa only [sub_zero] using box_anchor_physical_bound R n phase a ha)

#print axioms uniform_good
#print axioms ordered_mass
end
end ExceptionalTimes.OrderedGoodSewing
