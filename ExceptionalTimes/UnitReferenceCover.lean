import ExceptionalTimes.UnitStaticAttachment
import ExceptionalTimes.UnitMatchingTranslation
import ExceptionalTimes.IndependentAnnulusInput

/-! A concrete positively oriented finite cover of either unit matching
phase, together with an explicit positive-density grid in the reference
rectangle. These are deterministic geometry and counting statements. -/

open scoped Classical BigOperators
namespace ExceptionalTimes.UnitReferenceCover
noncomputable section
open PairSquareSewing UnitStaticAttachment

def offset (phase : Bool) : ℤ := if phase then 1 else 0

def left (phase : Bool) (v : Site) : Site :=
  (if (v.1+offset phase)%2=0 then v.1 else v.1-1,v.2)

theorem left_even (phase : Bool) (v : Site) : ((left phase v).1+offset phase)%2=0 := by
  dsimp [left]
  split <;> omega

def anchors (phase : Bool) (D : Finset Site) : Finset Site := D.image (left phase)

theorem anchor_even (phase : Bool) (D : Finset Site) (a : anchors phase D) :
    (a.val.1+offset phase)%2=0 := by
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp a.property
  rw [←hv]
  exact left_even phase v

def slot (phase : Bool) (D : Finset Site) : (anchors phase D)×Fin 2 ↪ Site where
  toFun ai := (ai.1.val.1+(ai.2.val:ℤ),ai.1.val.2)
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    have ha := anchor_even phase D a
    have hb := anchor_even phase D b
    have hi := i.isLt
    have hj := j.isLt
    dsimp at hfst hsnd
    have hij : i=j := Fin.ext (by omega)
    subst j
    have hab : a=b := Subtype.ext (Prod.ext (by omega) hsnd)
    subst b
    rfl

@[simp] theorem slot_zero (phase : Bool) (D : Finset Site) (a : anchors phase D) :
    slot phase D (a,0)=a.val := by
  change (a.val.1+(0:ℤ),a.val.2)=a.val
  simp

@[simp] theorem slot_one (phase : Bool) (D : Finset Site) (a : anchors phase D) :
    slot phase D (a,1)=a.val+(1,0) := by
  change (a.val.1+(1:ℤ),a.val.2)=a.val+(1,0)
  ext <;> simp

theorem slot_positive (phase : Bool) (D : Finset Site) (a : anchors phase D) :
    slot phase D (a,1)=slot phase D (a,0)+(1,0) := by simp

theorem slot_phase (phase : Bool) (D : Finset Site) (a : anchors phase D) :
    slot phase D (a,1)=UnitMatchingTranslation.partner phase (slot phase D (a,0)) := by
  have ha := anchor_even phase D a
  rw [slot_zero,slot_one]
  change a.val+(1,0)=(if (a.val.1+offset phase)%2=0 then a.val+(1,0) else a.val-(1,0))
  rw [ite_eq_left ha]

theorem slot_covers (phase : Bool) (D : Finset Site) :
    ∀ v∈D,∃ ai,slot phase D ai=v := by
  intro v hv
  let a : anchors phase D := ⟨left phase v,Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩
  by_cases h : (v.1+offset phase)%2=0
  · refine ⟨(a,0),?_⟩
    rw [slot_zero]
    simp [a,left,h]
  · refine ⟨(a,1),?_⟩
    rw [slot_one]
    ext <;> simp [a,left,h]

def gridAnchor (phase : Bool) {m : ℕ} (i : Fin m×Fin m) : Site :=
  (2*(i.1.val:ℤ)+offset phase,(i.2.val:ℤ))

theorem gridAnchor_injective (phase : Bool) (m : ℕ) :
    Function.Injective (@gridAnchor phase m) := by
  intro i j h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;> apply Fin.ext <;> dsimp [gridAnchor] at h1 h2 <;> omega

theorem gridAnchor_even (phase : Bool) {m : ℕ} (i : Fin m×Fin m) :
    ((gridAnchor phase i).1+offset phase)%2=0 := by
  dsimp [gridAnchor]
  omega

theorem left_gridAnchor (phase : Bool) {m : ℕ} (i : Fin m×Fin m) :
    left phase (gridAnchor phase i)=gridAnchor phase i := by
  simp [left,gridAnchor_even]

theorem bulk_mem_reference_support (e : ℝ) (he : 0<e) (x : Site) (hx : Bulk e x) :
    x∈(sourceReferenceAt e he 0).support := by
  have hphys : position e x∈sourcePhysicalMap e he '' (sourceReferenceAt e he 0).carrier := by
    rw [sourceReferenceAt_carrier]
    refine ⟨position e x,?_,?_⟩
    · have hx1 := abs_le.mp hx.1
      have hx2 := abs_le.mp hx.2
      constructor <;> constructor <;> linarith
    · have h0 : position e (0 : Site)=0 := by
        apply Complex.ext <;> simp [position,triangularEmbedding]
      simp [h0]
  obtain ⟨p,hp,heq⟩ := hphys
  have hp' : p=HexCells.center x := (sourcePhysicalMap e he).injective
    (heq.trans (sourcePhysicalMap_center e he x).symm)
  rw [PolygonQuad.mem_support]
  exact ⟨HexCells.center x,HexCells.center_mem_cell x,hp' ▸ hp⟩

theorem gridAnchor_bulk (phase : Bool) {m : ℕ} (i : Fin m×Fin m)
    (e : ℝ) (he : 0<e) (hem : e*(m:ℝ)≤1/64) : Bulk e (gridAnchor phase i) := by
  have hi : (i.1.val:ℝ)<m := by exact_mod_cast i.1.isLt
  have hj : (i.2.val:ℝ)<m := by exact_mod_cast i.2.isLt
  have hoff : 0≤offset phase ∧ offset phase≤1 := by cases phase <;> norm_num [offset]
  have hx0 : 0≤((gridAnchor phase i).1:ℝ) := by dsimp [gridAnchor]; exact_mod_cast (by omega : 0≤2*(i.1.val:ℤ)+offset phase)
  have hx : ((gridAnchor phase i).1:ℝ)≤2*m := by
    exact_mod_cast (show (gridAnchor phase i).1≤2*(m:ℤ) from by dsimp [gridAnchor]; omega)
  have hy0 : 0≤((gridAnchor phase i).2:ℝ) := by dsimp [gridAnchor]; positivity
  have hy : ((gridAnchor phase i).2:ℝ)≤m := by exact hj.le
  have hs0 := Real.sqrt_nonneg (3:ℝ)
  have hs2 : Real.sqrt (3:ℝ)≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  have hrex : e*((gridAnchor phase i).1:ℝ)≤2*(e*m) := by nlinarith
  have hrey : e*((gridAnchor phase i).2:ℝ)≤e*m := mul_le_mul_of_nonneg_left hy he.le
  have him : e*(Real.sqrt 3*((gridAnchor phase i).2:ℝ)/2)≤e*m := by
    have hs := mul_le_mul_of_nonneg_right hs2 hy0
    nlinarith
  unfold Bulk
  simp only [position,triangularEmbedding,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  constructor
  · rw [abs_of_nonneg (by positivity)]
    nlinarith
  · rw [abs_of_nonneg (by positivity)]
    nlinarith

def gridInCover (phase : Bool) (e : ℝ) (he : 0<e) (m : ℕ)
    (hem : e*(m:ℝ)≤1/64) : Fin m×Fin m ↪ anchors phase (sourceReferenceAt e he 0).support where
  toFun i := ⟨gridAnchor phase i,Finset.mem_image.mpr
    ⟨gridAnchor phase i,bulk_mem_reference_support e he _ (gridAnchor_bulk phase i e he hem),
      left_gridAnchor phase i⟩⟩
  inj' := fun _ _ h => gridAnchor_injective phase m (congrArg Subtype.val h)

#print axioms slot_phase
#print axioms slot_covers
#print axioms gridInCover
end
end ExceptionalTimes.UnitReferenceCover
