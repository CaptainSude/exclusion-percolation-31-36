import ExceptionalTimes.ForestRelabel
import ExceptionalTimes.CanonicalForestNumeric

/-! Common root and free-anchor labels for all ordered insertion sets.
The finite graph labels carry no information beyond the original anchors. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.RootedAnchorLabels

open PairSquareSewing ForestRelabel ForestAnchorIntegration ForestArmRadial
open ForestLatticeFamily ForestCounting ForestIntegration

variable {I I' J A X : Type*} [Fintype I] [Fintype I'] [Fintype J]

noncomputable def selectedFreeEquiv : {v : I ⊕ J // ¬selectedRoot v} ≃ I where
  toFun v := match v with
    | ⟨Sum.inl i,_⟩ => i
    | ⟨Sum.inr j,h⟩ => False.elim (h ⟨j,rfl⟩)
  invFun i := ⟨Sum.inl i,by rintro ⟨j,h⟩; cases h⟩
  left_inv v := by
    rcases v with ⟨v,hv⟩
    cases v with
    | inl i => rfl
    | inr j => exact False.elim (hv ⟨j,rfl⟩)
  right_inv _ := rfl

omit [Fintype I] [Fintype I'] [Fintype J] in
theorem selectedRoot_sumCongr (e : I ≃ I') (v : I' ⊕ J) :
    selectedRoot ((Equiv.sumCongr e (Equiv.refl J)).symm v) ↔ selectedRoot v := by
  cases v <;> simp [selectedRoot]

noncomputable def labels (k : ℕ) (J : Type*) [Fintype J] :
    (Fin k ⊕ J) ≃ Fin (k+Fintype.card J) :=
  (Equiv.sumCongr (Equiv.refl (Fin k)) (Fintype.equivFin J)).trans finSumFinEquiv

noncomputable def fixed (k : ℕ) (J : Type*) [Fintype J] : Fin (k+Fintype.card J) → Prop :=
  fun v => selectedRoot ((labels k J).symm v)

noncomputable def roots (k : ℕ) (J : Type*) [Fintype J] :
    {v // fixed k J v} ≃ J :=
  (rootEquiv (labels k J) selectedRoot).trans selectedRootEquiv

noncomputable def free (k : ℕ) (J : Type*) [Fintype J] :
    {v // ¬fixed k J v} ≃ Fin k :=
  (freeEquiv (labels k J) selectedRoot).trans selectedFreeEquiv

theorem roots_card (k : ℕ) : Fintype.card {v // fixed k J v}=Fintype.card J :=
  Fintype.card_congr (roots k J)

noncomputable def orderedLabels {k : ℕ} (order : Fin k ≃ I) :
    (I ⊕ J) ≃ Fin (k+Fintype.card J) :=
  (Equiv.sumCongr order.symm (Equiv.refl J)).trans (labels k J)

omit [Fintype I] in
theorem orderedLabels_fixed {k : ℕ} (order : Fin k ≃ I) (v : Fin (k+Fintype.card J)) :
    selectedRoot ((orderedLabels (J := J) order).symm v) ↔ fixed k J v :=
  selectedRoot_sumCongr order.symm ((labels k J).symm v)

noncomputable def anchorPosition (k : ℕ) (position : A → X) (root : J → X) (x : Fin k → A) :
    Fin (k+Fintype.card J) → X :=
  assignedPosition (fixed k J) position (fun v => root (roots k J v)) (fun v => x (free k J v))

omit [Fintype I] [Fintype J] in
theorem sumPosition_eq_assigned (position : I → X) (root : J → X) :
    (Sum.elim position root)=assignedPosition selectedRoot id
      (fun v => root (selectedRootEquiv v)) (fun v => position (selectedFreeEquiv v)) := by
  funext v
  cases v with
  | inl i => simp [assignedPosition,selectedRoot,selectedFreeEquiv]
  | inr j => simp [assignedPosition,selectedRoot,selectedRootEquiv]

theorem anchorPosition_eq (k : ℕ) (position : A → X) (root : J → X) (x : Fin k → A) :
    anchorPosition k position root x=
      fun v => Sum.elim (fun i => position (x i)) root ((labels k J).symm v) := by
  rw [sumPosition_eq_assigned]
  exact assignedPosition_map (labels k J) selectedRoot position
    (fun v => root (selectedRootEquiv v)) (fun v => x (selectedFreeEquiv v))

omit [Fintype I] in
theorem orderedPosition_eq {k : ℕ} (order : Fin k ≃ I)
    (position : I → X) (root : J → X) :
    (fun v => Sum.elim position root ((orderedLabels (J := J) order).symm v))=
      anchorPosition k id root (fun i => position (order i)) := by
  rw [anchorPosition_eq]
  funext v
  cases h : (labels k J).symm v <;> simp [orderedLabels,h]

variable [Fintype A]

theorem sum_anchorPosition (k : ℕ) (position : A → X) (root : J → X)
    (F : (Fin (k+Fintype.card J) → X) → ℝ) :
    (∑ x : Fin k → A,F (anchorPosition k position root x))=
      ∑ y : {v // ¬fixed k J v} → A,
        F (assignedPosition (fixed k J) position (fun v => root (roots k J v)) y) := by
  let e := Equiv.arrowCongr (free k J).symm (Equiv.refl A)
  exact e.sum_comp (fun y => F (assignedPosition (fixed k J) position
    (fun v => root (roots k J v)) y))

#print axioms orderedPosition_eq
#print axioms sum_anchorPosition

end ExceptionalTimes.RootedAnchorLabels
