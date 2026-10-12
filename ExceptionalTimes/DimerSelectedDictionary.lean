import ExceptionalTimes.SelectedKernelLaw
import ExceptionalTimes.CanonicalLifeStatic
import ExceptionalTimes.DimerExpansion

/-! Exact history-coordinate and site-overwrite dictionary for the
selected coefficients of the finite dimer product expansion. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.DimerSelectedDictionary

open DimerLaw DimerExpansion CenteredBlocks BlockExpansion EnvironmentVariance
open PairSquareSewing ActivePartitionLaw CanonicalSpatialProduct SelectedKernelLaw

def historyEquiv : History ≃ (Bool → Color) where
  toFun h t := if t then h.2 else h.1
  invFun h := (h false,h true)
  left_inv h := rfl
  right_inv h := by funext t; cases t <;> rfl

theorem history_kernel {I : Type*} [Fintype I] (u : I → History → ℝ)
    (F : (I → History) → ℝ) :
    kernel u F=kernel (fun i h => u i (historyEquiv.symm h))
      (fun h => F (fun i => historyEquiv.symm (h i))) := by
  let e := Equiv.piCongrRight (fun _ : I => historyEquiv)
  unfold kernel
  rw [←e.symm.sum_comp]
  rfl

theorem history_sum (u : History → ℝ) :
    (∑ h : Bool → Color,u (historyEquiv.symm h))=∑ h : History,u h :=
  historyEquiv.symm.sum_comp u

theorem history_variation (u : History → ℝ) :
    variation (fun h : Bool → Color => u (historyEquiv.symm h))=variation u :=
  historyEquiv.symm.sum_comp (fun h => |u h|)

variable {B : Type*}

def selectedSlot (slot : B × Fin 2 ↪ Site) (S : Finset B) : S × Fin 2 ↪ Site where
  toFun ie := slot (ie.1.val,ie.2)
  inj' := by
    rintro ⟨i,e⟩ ⟨j,f⟩ h
    have hh := slot.injective h
    have hij : i=j := Subtype.ext (congrArg Prod.fst hh)
    have hef : e=f := congrArg Prod.snd hh
    exact Prod.ext hij hef

theorem pairDecode_at (slot : B × Fin 2 ↪ Site) (x : B → Color) (be : B × Fin 2) :
    pairDecode slot x (slot be)=x be.1 be.2 := slot.injective.extend_apply _ _ _

theorem pairDecode_off (slot : B × Fin 2 ↪ Site) (x : B → Color) {v : Site}
    (hv : v∉Set.range slot) : pairDecode slot x v=false := Function.extend_apply' _ _ _ hv

theorem selectedSlot_range (slot : B × Fin 2 ↪ Site) (S : Finset B) (b : B) (e : Fin 2) :
    slot (b,e)∈Set.range (selectedSlot slot S) ↔ b∈S := by
  constructor
  · rintro ⟨⟨i,f⟩,h⟩
    have hh := congrArg Prod.fst (slot.injective h)
    exact (show i.val=b from hh) ▸ i.property
  · intro h
    exact ⟨(⟨b,h⟩,e),rfl⟩

variable [Fintype B]

theorem selected_overwrite_configuration (slot : B × Fin 2 ↪ Site) (S : Finset B)
    (o : (B → Color) × (B → Color)) (h : S → Bool → Color) (t : Bool) :
    canonicalBackground slot
      (pairCoordinates.symm (overwrite S (pairCoordinates o) (fun i => historyEquiv.symm (h i)))) t=
      overwriteDimers (selectedSlot slot S) (canonicalBackground slot o t) (fun i => h i t) := by
  funext v
  by_cases hv : v∈Set.range slot
  · obtain ⟨⟨b,e⟩,rfl⟩ := hv
    by_cases hb : b∈S
    · have hs : slot (b,e)=selectedSlot slot S (⟨b,hb⟩,e) := rfl
      rw [hs,overwriteDimers_endpoint]
      change pairDecode slot _ (slot (b,e))=_
      rw [pairDecode_at]
      have hj := join_inside S (fun i => historyEquiv.symm (h i))
        (fun b => pairCoordinates o b.val) ⟨b,hb⟩
      cases t
      · exact congrArg (fun q : History => q.1 e) hj
      · exact congrArg (fun q : History => q.2 e) hj
    · have hs : slot (b,e)∉Set.range (selectedSlot slot S) := by
        simpa only [selectedSlot_range] using hb
      rw [overwriteDimers_outside _ _ _ hs]
      change pairDecode slot _ (slot (b,e))=pairDecode slot _ (slot (b,e))
      rw [pairDecode_at,pairDecode_at]
      have hj := join_outside S (fun i => historyEquiv.symm (h i))
        (fun b => pairCoordinates o b.val) ⟨b,hb⟩
      cases t
      · exact congrArg (fun q : History => q.1 e) hj
      · exact congrArg (fun q : History => q.2 e) hj
  · have hs : v∉Set.range (selectedSlot slot S) := by
      rintro ⟨⟨i,e⟩,hi⟩
      exact hv ⟨(i.val,e),hi⟩
    rw [overwriteDimers_outside _ _ _ hs]
    exact (pairDecode_off slot _ hv).trans (pairDecode_off slot _ hv).symm

theorem selected_coefficient_actual_overwrites (slot : B × Fin 2 ↪ Site)
    (p : B → ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (u : B → History → ℝ) (S : Finset B) (F : TwoTimeConfiguration → ℝ) :
    selectedKernel (fun b h => twoTimeWeight (p b) h.1 h.2) u S
      (fun h => F (canonicalBackground slot (pairCoordinates.symm h)))=
      (ManyDimerLaw.manyLaw p hp0 hp1).expect (fun o =>
        kernel (fun i : S => fun h => u i.val (historyEquiv.symm h))
          (fun h => F (fun t => overwriteDimers (selectedSlot slot S)
            (canonicalBackground slot o t) (fun i => h i t)))) := by
  rw [canonical_selected_coefficient p hp0 hp1 u S (fun o => F (canonicalBackground slot o))]
  apply FiniteLaw.expect_congr
  intro o
  rw [history_kernel]
  unfold kernel
  apply Finset.sum_congr rfl
  intro h _
  congr 2
  dsimp only
  apply congrArg F
  funext t
  exact selected_overwrite_configuration slot S o h t

#print axioms selected_coefficient_actual_overwrites

end ExceptionalTimes.DimerSelectedDictionary
