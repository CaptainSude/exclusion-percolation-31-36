import ExceptionalTimes.ActivePartitionLaw
import ExceptionalTimes.HalfPlaneArms

/-! Uniform finite color averages are the literal iid fair-site law.
Unused vertices are integrated out and supported events are compared on
their exact original site coordinates. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.FiniteSiteLaw

noncomputable section

open DimerLaw FiniteHaar EnvironmentVariance ProbeProduct
open ActivePartitionLaw MixedAnnularCollar MixedCanonicalLaw PairSquareSewing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance {A O : Type*} : DecidableEq (A ⊕ O) :=
  fun a b => Classical.propDecidable (a = b)

theorem fairSites_expect_eq_average (D : Type*) [Fintype D] [DecidableEq D]
    (f : (D → Bool) → ℝ) : (fairSites D).expect f = average f := by
  simp only [FiniteLaw.expect,fairSites,FiniteLaw.pi,fairBit,average,
    Finset.prod_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat,
    one_div,inv_pow,Finset.mul_sum]

theorem average_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    average f = average (fun x => average (fun y => f (x,y))) := by
  simp only [average,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,
    Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem average_sum_left {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V]
    (F : (U → Bool) → ℝ) :
    average (fun x : U ⊕ V → Bool => F (fun u => x (.inl u))) = average F := by
  have h := average_equiv (Equiv.sumArrowEquivProdArrow U V Bool)
    (fun x => F x.1)
  exact h.trans (by rw [average_prod]; simp only [average_const])

theorem average_restrict {B C : Type*} [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C]
    (f : C ↪ B) (F : (C → Bool) → ℝ) :
    average (fun x : B → Bool => F (fun c => x (f c))) = average F := by
  let Z := {b : B // b ∉ Set.range f}
  let e : C ⊕ Z ≃ B :=
    (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl Z)).trans
      (Equiv.sumCompl (fun b => b ∈ Set.range f))
  have he (c : C) : e (.inl c) = f c := rfl
  have h := average_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
    (fun x => F (fun c => x (f c)))
  apply h.symm.trans
  have hf : (fun x : C ⊕ Z → Bool =>
      F (fun c => (Equiv.arrowCongr e (Equiv.refl Bool) x) (f c))) =
      (fun x : C ⊕ Z → Bool => F (fun c => x (.inl c))) := by
    funext x
    change (F fun c => x (e.symm (f c))) = _
    simp only [← he,Equiv.symm_apply_apply]
  rw [hf]
  exact average_sum_left F

def curryColors (B : Type*) : ((B × Fin 2) → Bool) ≃ (B → Color) where
  toFun x b k := x (b,k)
  invFun x b := x b.1 b.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem average_pairDecode {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (F : Configuration → ℝ) :
    average (fun x => F (pairDecode slot x)) =
      average (fun x : B × Fin 2 → Bool =>
        F (Function.extend slot x (fun _ => false))) :=
  (average_equiv (curryColors B) (fun x => F (pairDecode slot x))).symm

theorem completeColors_agrees (D : Finset Site) (x : D → Bool) (v : D) :
    completeColors D x v = x v := by simp [completeColors]

/-- An arbitrary finite injective site enumeration has the original fair
law on every supported local real test; the remaining sites are summed out. -/
theorem average_site_embedding {B : Type*} [Fintype B]
    [DecidableEq B]
    (slot : B ↪ Site) (D : Finset Site)
    (hcover : ∀ v ∈ D, ∃ b, slot b = v) (F : Configuration → ℝ)
    (hlocal : ∀ ω η, (∀ v ∈ D, ω v = η v) → F ω = F η) :
    average (fun x : B → Bool => F (Function.extend slot x (fun _ => false))) =
      (fairSites D).expect (fun x => F (completeColors D x)) := by
  let select : D ↪ B :=
    ⟨fun v => Classical.choose (hcover v.val v.property),by
      intro v w h
      have hv := Classical.choose_spec (hcover v.val v.property)
      have hw := Classical.choose_spec (hcover w.val w.property)
      exact Subtype.ext (hv.symm.trans ((congrArg slot h).trans hw))⟩
  have hs (v : D) : slot (select v) = v.val := Classical.choose_spec (hcover v.val v.property)
  have he (x : B → Bool) : F (Function.extend slot x (fun _ => false)) =
      F (completeColors D (fun v => x (select v))) := by
    apply hlocal
    intro v hv
    have hv' : slot (select ⟨v,hv⟩) = v := hs ⟨v,hv⟩
    rw [← hv',slot.injective.extend_apply]
    rw [hv']
    exact (completeColors_agrees D (fun w => x (select w)) ⟨v,hv⟩).symm
  simp_rw [he]
  rw [fairSites_expect_eq_average]
  exact average_restrict select (fun x => F (completeColors D x))

/-- Static source-law dictionary for the original matching decoder. -/
theorem average_pairDecode_fairSites {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀ v ∈ D, ∃ b, slot b = v) (E : Configuration → Prop)
    (hlocal : ∀ ω η, (∀ v ∈ D, ω v = η v) → (E ω ↔ E η)) :
    average (fun x => indicator (E (pairDecode slot x))) =
      probability (fairSites D) (fun x => E (completeColors D x)) := by
  rw [average_pairDecode slot (fun ω => indicator (E ω))]
  exact average_site_embedding slot D hcover (fun ω => indicator (E ω))
    (fun ω η he => congrArg indicator (propext (hlocal ω η he)))

/-- Static source-law dictionary for the active/exterior decoder used by
the collar comparison. It applies to any finite support inside the slot. -/
theorem average_splitDecode_fairSites {A O : Type*} [Fintype A] [Fintype O]
    (slot : ((A ⊕ O) × Fin 2) ↪ Site) (D : Finset Site)
    (hcover : ∀ v ∈ D, ∃ b, slot b = v) (E : Configuration → Prop)
    (hlocal : ∀ ω η, (∀ v ∈ D, ω v = η v) → (E ω ↔ E η)) :
    average (fun x => indicator (E (splitDecode slot x))) =
      probability (fairSites D) (fun x => E (completeColors D x)) := by
  have h := average_equiv (Equiv.sumArrowEquivProdArrow A O Color)
    (fun x => indicator (E (splitDecode slot x)))
  apply h.symm.trans
  have he : (fun x : A ⊕ O → Color =>
      indicator (E (splitDecode slot ((Equiv.sumArrowEquivProdArrow A O Color) x)))) =
      (fun x => indicator (E (pairDecode slot x))) := by
    funext x
    congr 2
    unfold splitDecode pairDecode
    congr 1
    funext s
    rcases s with ⟨a,k⟩
    cases a <;> rfl
  rw [he]
  exact average_pairDecode_fairSites slot D hcover E hlocal

#print axioms fairSites_expect_eq_average
#print axioms average_restrict
#print axioms average_pairDecode_fairSites
#print axioms average_splitDecode_fairSites

end

end ExceptionalTimes.FiniteSiteLaw
