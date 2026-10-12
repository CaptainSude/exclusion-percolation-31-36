import ExceptionalTimes.DimerSelectedDictionary

/-! The expansion base is the literal static fair-site law. At parameter
zero both dimer times are identical; decoding and marginalizing unused sites
matches the raw finite iid field used by the polygon sewing inputs. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.DimerBaseField

open DimerLaw DimerExpansion ManyDimerLaw EnvironmentVariance FiniteHaar
open PairSquareSewing ActivePartitionLaw DimerSelectedDictionary ProbeProduct CenteredBlocks

variable {B : Type*} [Fintype B]

theorem twoTimeWeight_zero (x y : Color) :
    twoTimeWeight 0 x y=if x=y then (1/4:ℝ) else 0 := by
  by_cases h : x=y <;> simp [twoTimeWeight,h]

theorem manyWeight_zero (x y : B → Color) :
    manyWeight (fun _ => 0) x y=if x=y then (4:ℝ)⁻¹^Fintype.card B else 0 := by
  by_cases h : x=y
  · subst y
    simp [manyWeight,twoTimeWeight_zero]
  · rw [ite_eq_right h]
    obtain ⟨b,hb⟩ : ∃ b,x b≠y b := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [twoTimeWeight_zero,hb])

theorem manyLaw_zero_expect (F : ((B → Color) × (B → Color)) → ℝ) :
    (manyLaw (fun _ : B => 0) (fun _ => le_rfl) (fun _ => by norm_num)).expect F=
      average (fun x => F (x,x)) := by
  simp only [FiniteLaw.expect,manyLaw,Fintype.sum_prod_type,manyWeight_zero,average]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←Finset.mul_sum]
  congr 1
  simp

omit [Fintype B] in
theorem canonicalBackground_diagonal (slot : B × Fin 2 ↪ Site) (x : B → Color) :
    canonicalBackground slot (x,x)=fun _ => pairDecode slot x := by
  funext t
  cases t <;> rfl

theorem base_field_expect (slot : B × Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀ v∈D,∃ be,slot be=v) (F : TwoTimeConfiguration → ℝ)
    (hlocal : ∀ ω η : Configuration,(∀ v∈D,ω v=η v) → F (fun _ => ω)=F (fun _ => η)) :
    (manyLaw (fun _ : B => 0) (fun _ => le_rfl) (fun _ => by norm_num)).expect
      (fun o => F (canonicalBackground slot o))=
      (fairSites D).expect (fun x => F (fun _ => completeColors D x)) := by
  rw [manyLaw_zero_expect]
  simp only [canonicalBackground_diagonal]
  rw [FiniteSiteLaw.average_pairDecode slot (fun ω => F (fun _ => ω))]
  exact FiniteSiteLaw.average_site_embedding slot D hcover (fun ω => F (fun _ => ω)) hlocal

theorem overwrite_agrees_on {I : Type*} (endpoint : I × Fin 2 ↪ Site)
    (D : Finset Site) (ω η : Configuration) (h : ∀ v∈D,ω v=η v) (a : I → Color) :
    ∀ v∈D,overwriteDimers endpoint ω a v=overwriteDimers endpoint η a v := by
  intro v hv
  by_cases he : v∈Set.range endpoint
  · obtain ⟨⟨i,e⟩,rfl⟩ := he
    rw [overwriteDimers_endpoint,overwriteDimers_endpoint]
  · rw [overwriteDimers_outside _ _ _ he,overwriteDimers_outside _ _ _ he]
    exact h v hv

theorem selected_coefficient_fair_overwrites (slot : B × Fin 2 ↪ Site)
    (D : Finset Site) (hcover : ∀ v∈D,∃ be,slot be=v)
    (u : B → History → ℝ) (S : Finset B) (F : TwoTimeConfiguration → ℝ)
    (hlocal : ∀ ω η : TwoTimeConfiguration,(∀ t v,v∈D → ω t v=η t v) → F ω=F η) :
    BlockExpansion.selectedKernel (fun _ => base) u S
      (fun h => F (canonicalBackground slot (CanonicalSpatialProduct.pairCoordinates.symm h)))=
      (fairSites D).expect (fun x =>
        kernel (fun i : S => fun h => u i.val (historyEquiv.symm h))
          (fun h => F (fun t => overwriteDimers (selectedSlot slot S)
            (completeColors D x) (fun i => h i t)))) := by
  rw [show (fun _ : B => base)=(fun _ h => twoTimeWeight 0 h.1 h.2) from rfl]
  rw [selected_coefficient_actual_overwrites slot (fun _ => 0)
    (fun _ => le_rfl) (fun _ => by norm_num) u S F]
  apply base_field_expect slot D hcover
    (fun ω => kernel (fun i : S => fun h => u i.val (historyEquiv.symm h))
      (fun h => F (fun t => overwriteDimers (selectedSlot slot S) (ω t) (fun i => h i t))))
  intro ω η he
  unfold kernel
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  apply hlocal
  intro t v hv
  exact overwrite_agrees_on (selectedSlot slot S) D ω η he (fun i => h i t) v hv

theorem selected_coefficient_extended_base {C : Type*} [Fintype C]
    (slot : B × Fin 2 ↪ Site) (exterior : C × Fin 2 ↪ Site)
    (D : Finset Site) (hcover : ∀ v∈D,∃ be,slot be=v)
    (hext : ∀ v∈D,∃ ce,exterior ce=v)
    (u : B → History → ℝ) (S : Finset B) (F : TwoTimeConfiguration → ℝ)
    (hlocal : ∀ ω η : TwoTimeConfiguration,(∀ t v,v∈D → ω t v=η t v) → F ω=F η) :
    BlockExpansion.selectedKernel (fun _ => base) u S
      (fun h => F (canonicalBackground slot (CanonicalSpatialProduct.pairCoordinates.symm h)))=
      (manyLaw (fun _ : C => 0) (fun _ => le_rfl) (fun _ => by norm_num)).expect (fun o =>
        kernel (fun i : S => fun h => u i.val (historyEquiv.symm h))
          (fun h => F (fun t => overwriteDimers (selectedSlot slot S)
            (canonicalBackground exterior o t) (fun i => h i t)))) := by
  rw [selected_coefficient_fair_overwrites slot D hcover u S F hlocal]
  symm
  apply base_field_expect exterior D hext
    (fun ω => kernel (fun i : S => fun h => u i.val (historyEquiv.symm h))
      (fun h => F (fun t => overwriteDimers (selectedSlot slot S) (ω t) (fun i => h i t))))
  intro ω η he
  unfold kernel
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  apply hlocal
  intro t v hv
  exact overwrite_agrees_on (selectedSlot slot S) D ω η he (fun i => h i t) v hv

#print axioms selected_coefficient_extended_base
#print axioms selected_coefficient_fair_overwrites

end ExceptionalTimes.DimerBaseField


